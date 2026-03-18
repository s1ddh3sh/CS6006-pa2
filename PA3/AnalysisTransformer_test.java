import java.util.*;

import polyglot.ast.Return;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.toolkits.graph.*;
import soot.jimple.toolkits.callgraph.Edge;

public class AnalysisTransformer_test extends SceneTransformer {
    static CallGraph cg;
    private static final AllocSite UNKNOWN_ALLOC = new AllocSite(-1, true, -1);
    // private static boolean initialized = false;
    private static final Map<AllocSite, EscapeStatus> escapeStatus = new HashMap<>();
    private static final Map<AllocSite, Set<Integer>> rewriteLines = new HashMap<>();

    private static final Map<Integer, AllocSite> totalAllocSites = new HashMap<>();

    private static int totalTargets = 0;
    private static int processedTargets = 0;

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        cg = Scene.v().getCallGraph();

        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootMethod method : sc.getMethods()) {
                if (shouldAnalyze(method)) {
                    totalTargets++;
                    analyzeMethod(method);
                }
            }
        }

        if (totalTargets == processedTargets)
            printResults();
    }

    private void printResults() {
        for (Map.Entry<Integer, AllocSite> entry : totalAllocSites.entrySet()) {
            AllocSite info = entry.getValue();
            EscapeStatus status = escapeStatus.getOrDefault(info, EscapeStatus.LOCAL);

            String prefix = "O" + info.lineNumber + " = ";

            if (status == EscapeStatus.ESCAPED) {
                System.out.println(prefix + "N");
            } else {
                Set<Integer> lines = rewriteLines.getOrDefault(info, new HashSet<>());
                if (lines.isEmpty()) {
                    System.out.println(prefix + "Y[]");
                } else {
                    System.out.println(prefix + "Y" + lines.toString()
                            .replace(" ", ""));
                }
            }
        }
    }

    // }
    void analyzeMethod(SootMethod method) {

        Body body = method.retrieveActiveBody();

        UnitGraph graph = new BriefUnitGraph(body);
        Map<Unit, PointsToState> ptsIn = new HashMap<>();
        Map<Unit, PointsToState> ptsOut = new HashMap<>();
        runPointsToAnalysis(graph, ptsIn, ptsOut, method, false);
        processedTargets++;
    }

    enum EscapeStatus {
        LOCAL(0),
        REWRITE(1),
        ESCAPED(2);

        private int level;

        EscapeStatus(int level) {
            this.level = level;
        }

        public int getLevel() {
            return level;
        }

        public boolean greaterThan(EscapeStatus other) {
            return this.level > other.level;
        }

    }

    private static boolean shouldAnalyze(SootMethod method) {
        if (method == null || !method.isConcrete() || method.isPhantom()) {
            return false;
        }
        if (method.getDeclaringClass().isLibraryClass()) {
            return false;
        }
        String name = method.getName();
        return !"<clinit>".equals(name);
    }

    private static void runPointsToAnalysis(
            UnitGraph graph,
            Map<Unit, PointsToState> inMap,
            Map<Unit, PointsToState> outMap, SootMethod method, boolean isCallee) {

        for (Unit unit : graph) {
            if (!inMap.containsKey(unit))
                inMap.put(unit, PointsToState.empty());
            outMap.put(unit, PointsToState.empty());
        }

        // if (isCallee) {
        //     runEscapeAnalysis(graph, inMap);
        // }

        Deque<Unit> worklist = new ArrayDeque<>();
        Set<Unit> visited = new HashSet<>();
        for (Unit unit : graph) {
            worklist.add(unit);
        }

        while (!worklist.isEmpty()) {
            Unit unit = worklist.removeFirst();
            PointsToState inState = mergePointsTo(graph.getPredsOf(unit), outMap, visited);
            PointsToState outState = transferPointsTo(unit, inState);
            visited.add(unit);
            if (!outState.equals(outMap.get(unit))) {
                inMap.put(unit, inState);
                outMap.put(unit, outState);
                System.out.println("\nUnit: " + unit);
                printPointsToState("IN", inState);
                printPointsToState("OUT", outState);
                for (Unit succ : graph.getSuccsOf(unit)) {
                    worklist.add(succ);
                }
            } else {
                inMap.put(unit, inState);
            }

        }
    }

    private static PointsToState mergePointsTo(
            List<Unit> preds, Map<Unit, PointsToState> outMap, Set<Unit> visited) {
        if (preds == null || preds.isEmpty()) {
            return PointsToState.empty();
        }
        PointsToState merged = null;
        for (Unit pred : preds) {
            if (!visited.contains(pred)) {
                continue;
            }
            PointsToState state = outMap.get(pred);
            if (merged == null) {
                merged = state.copy();
            } else {
                merged = merged.union(state);
            }
        }
        return merged == null ? PointsToState.empty() : merged;
    }

    private static void processInvokeExpr(PointsToState state, InvokeExpr invokeExpr, Unit callUnit) {

        Iterator<Edge> edges = cg.edgesOutOf(callUnit);

        if (!edges.hasNext())
            return;

        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod target = edge.tgt();

            if (!shouldAnalyze(target))
                continue;

            PointsToState calleeState = buildCalleeState(state, invokeExpr, target);

            Body calleeBody = target.retrieveActiveBody();
            UnitGraph graph = new BriefUnitGraph(calleeBody);

            Map<Unit, PointsToState> calleePtsIn = new HashMap<>();
            Map<Unit, PointsToState> calleePtsOut = new HashMap<>();

            Unit firstUnit = calleeBody.getUnits().getFirst();
            calleePtsIn.put(firstUnit, calleeState);

            runPointsToAnalysis(graph, calleePtsIn, calleePtsOut, target, true);

            Unit lastUnit = calleeBody.getUnits().getLast();
            PointsToState calleeOutState = calleePtsOut.get(lastUnit);

            mergeCalleeState(state, calleeOutState, invokeExpr, target);
        }

        // receiver
        if (invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr instanceInvoke = (InstanceInvokeExpr) invokeExpr;
            Value base = instanceInvoke.getBase();
            if (base instanceof Local) {
                Set<AllocSite> basePts = state.getVar((Local) base);
                for (AllocSite site : basePts) {
                    rewriteLines.computeIfAbsent(site, k -> new HashSet<>())
                            .add(callUnit.getJavaSourceStartLineNumber());
                }
            }
        }

        // args
        List<Value> args = invokeExpr.getArgs();

        for (int i = 0; i < args.size(); i++) {
            Value arg = args.get(i);
            if (arg instanceof Local) {
                Set<AllocSite> argPts = state.getVar((Local) arg);
                for (AllocSite site : argPts) {
                    rewriteLines.computeIfAbsent(site, k -> new HashSet<>())
                            .add(callUnit.getJavaSourceStartLineNumber());
                }
            }
        }
    }

    private static void mergeCalleeState(PointsToState callerState, PointsToState calleeState, InvokeExpr invokeExpr,
            SootMethod target) {
        if (calleeState == null)
            return;

        Set<AllocSite> passedSites = new HashSet<>();
        if (invokeExpr instanceof InstanceInvokeExpr) {
            Value receiver = ((InstanceInvokeExpr) invokeExpr).getBase();
            if (receiver instanceof Local) {
                Set<AllocSite> pts = callerState.getVar((Local) receiver);
                for (AllocSite site : pts) {
                    if (!site.equals(UNKNOWN_ALLOC))
                        passedSites.add(site);
                }
            }
        }

        for (Value arg : invokeExpr.getArgs()) {
            if (arg instanceof Local) {
                Set<AllocSite> pts = callerState.getVar((Local) arg);
                for (AllocSite site : pts) {
                    if (!site.equals(UNKNOWN_ALLOC))
                        passedSites.add(site);
                }
            }
        }

        Deque<AllocSite> worklist = new ArrayDeque<>(passedSites);
        Set<AllocSite> visited = new HashSet<>(passedSites);

        while (!worklist.isEmpty()) {
            AllocSite site = worklist.poll();
            for (SootField f : calleeState.getAllFields(site)) {
                for (AllocSite reachable : calleeState.getField(site, f)) {
                    if (!reachable.equals(UNKNOWN_ALLOC) && visited.add(reachable)) {
                        passedSites.add(reachable);
                        worklist.add(reachable);
                    }
                }
            }
        }

        for (AllocSite site : passedSites) {
            Set<SootField> calleeFields = calleeState.getAllFields(site);
            Set<SootField> callerFields = callerState.getAllFields(site);

            for (SootField field : calleeFields) {
                Set<AllocSite> calleeFieldPts = calleeState.getField(site, field);
                callerState.setField(site, field, calleeFieldPts);
            }

            for (SootField field : callerFields) {
                if (!calleeFields.contains(field)) {
                    callerState.setField(site, field, setOf(UNKNOWN_ALLOC));
                }
            }

        }
    }

    private static PointsToState buildCalleeState(PointsToState callerState, InvokeExpr invokeExpr, SootMethod target) {
        PointsToState calleeState = callerState.copy();

        Body calleeBody = target.retrieveActiveBody();

        // this ref
        if (invokeExpr instanceof InstanceInvokeExpr) {
            Value receiverVal = ((InstanceInvokeExpr) invokeExpr).getBase();

            if (receiverVal instanceof Local) {
                Set<AllocSite> receiverPts = callerState.getVar((Local) receiverVal);

                Local thisLocal = getThisLocal(calleeBody);

                if (thisLocal != null) {
                    calleeState.setVar(thisLocal, receiverPts);
                }
            }
        }
        // args
        List<Value> args = invokeExpr.getArgs();
        for (int i = 0; i < args.size(); i++) {
            Value arg = args.get(i);

            Set<AllocSite> argPts;
            if (arg instanceof Local) {
                argPts = callerState.getVar((Local) arg);
            } else {
                argPts = setOf(UNKNOWN_ALLOC);
            }
            Local paramLocal = getParamLocal(calleeBody, i);

            if (paramLocal != null) {
                calleeState.setVar(paramLocal, argPts);
            }
        }
        return calleeState;
    }

    private static Local getThisLocal(Body body) {
        for (Unit u : body.getUnits()) {
            if (!(u instanceof IdentityStmt))
                continue;
            IdentityStmt id = (IdentityStmt) u;
            if (id.getRightOp() instanceof ThisRef) {
                return (Local) id.getLeftOp();
            }
        }
        return null;
    }

    private static Local getParamLocal(Body body, int index) {
        for (Unit u : body.getUnits()) {
            if (!(u instanceof IdentityStmt))
                continue;
            IdentityStmt id = (IdentityStmt) u;
            if (id.getRightOp() instanceof ParameterRef) {
                ParameterRef pr = (ParameterRef) id.getRightOp();
                if (pr.getIndex() == index) {
                    return (Local) id.getLeftOp();
                }
            }
        }
        return null;
    }

    private static PointsToState transferPointsTo(
            Unit unit, PointsToState inState) {

        int line = unit.getJavaSourceStartLineNumber();
        PointsToState outState = inState.copy();
        if (unit instanceof IdentityStmt) {
            return outState;
        }

        if (unit instanceof InvokeStmt) {
            InvokeStmt invokeStmt = (InvokeStmt) unit;
            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
            processInvokeExpr(outState, invokeExpr, unit);
            return outState;
        }

        if (!(unit instanceof AssignStmt)) {
            return outState;
        }

        AssignStmt stmt = (AssignStmt) unit;
        Value lhs = stmt.getLeftOp();
        Value rhs = stmt.getRightOp();

        if (rhs instanceof InvokeExpr) {
            InvokeExpr invokeExpr = (InvokeExpr) rhs;
            processInvokeExpr(outState, invokeExpr, unit);

            if (lhs instanceof Local) {
                Local left = (Local) lhs;
                SootMethod met = invokeExpr.getMethod();
                Type returnType = met.getReturnType();
                if (!(returnType instanceof VoidType)) {
                }
                outState.recordWrite(left, line);
            }
            return outState;
        }

        if (lhs instanceof Local) {
            Local left = (Local) lhs;
            if (rhs instanceof AnyNewExpr) {
                outState.setVar(left, setOf(getAllocSite(line, unit)));
                escapeStatus.put(getAllocSite(line, unit), EscapeStatus.LOCAL);
                rewriteLines.put(getAllocSite(line, unit), new HashSet<>());
            } else if (rhs instanceof Local) {
                outState.setVar(left, outState.getVar((Local) rhs));
            } else if (rhs instanceof StaticFieldRef) {
                outState.setVar(left, setOf(UNKNOWN_ALLOC));
            } else if (rhs instanceof Constant) {
                outState.setVar(left, new HashSet<>());
            } else if (rhs instanceof InstanceFieldRef) {
                InstanceFieldRef fieldRef = (InstanceFieldRef) rhs;
                Local base = (Local) fieldRef.getBase();
                SootField field = fieldRef.getField();
                Set<AllocSite> basePts = outState.getVar(base);
                Set<AllocSite> result = new HashSet<>();
                boolean addUnknown = basePts.contains(UNKNOWN_ALLOC);
                for (AllocSite site : basePts) {
                    if (site.equals(UNKNOWN_ALLOC)) {
                        continue;
                    }
                    Set<AllocSite> fieldPts = outState.getField(site, field);
                    if (fieldPts.isEmpty()) {
                        addUnknown = true;
                    } else {
                        result.addAll(fieldPts);
                    }
                }
                if (addUnknown || result.isEmpty()) {
                    result.add(UNKNOWN_ALLOC);
                }
                outState.setVar(left, result);
            } else if (rhs instanceof Constant) {
                outState.setVar(left, setOf(UNKNOWN_ALLOC));
            } else {
                outState.setVar(left, setOf(UNKNOWN_ALLOC));
            }
            outState.recordWrite(left, line);
            return outState;
        }

        if (lhs instanceof InstanceFieldRef && (rhs instanceof Local || rhs instanceof Constant)) {
            InstanceFieldRef fieldRef = (InstanceFieldRef) lhs;
            Local base = (Local) fieldRef.getBase();
            SootField field = fieldRef.getField();
            Set<AllocSite> rhsPts;
            if (rhs instanceof Local) {
                rhsPts = outState.getVar((Local) rhs);
            } else {
                rhsPts = new HashSet<>();
            }

            Set<AllocSite> basePts = outState.getVar(base);
            boolean strong = basePts.size() == 1 && !basePts.contains(UNKNOWN_ALLOC);
            if (strong) {
                AllocSite site = basePts.iterator().next();
                outState.setField(site, field, rhsPts);
            } else {
                for (AllocSite site : basePts) {
                    if (!site.equals(UNKNOWN_ALLOC)) {
                        outState.addField(site, field, rhsPts);
                    }
                }
            }
        }

        return outState;
    }

    private static void printPointsToState(String label, PointsToState state) {
        System.out.println("  " + label + ":");
        if (state == null) {
            System.out.println("    [NULL STATE]");
            return;
        }

        Map<Local, Set<AllocSite>> varPts = state.varPts;
        if (varPts.isEmpty()) {
            System.out.println("    Variables: [EMPTY]");
        } else {
            System.out.println("    Variables:");
            for (Map.Entry<Local, Set<AllocSite>> entry : varPts.entrySet()) {
                Local var = entry.getKey();
                Set<AllocSite> sites = entry.getValue();
                System.out.println("      " + var.getName() + " -> {" + allocSiteSetStr(sites) + "}");
            }
        }

        Map<FieldKey, Set<AllocSite>> fieldPts = state.fieldPts;
        if (!fieldPts.isEmpty()) {
            System.out.println("    Fields:");
            for (Map.Entry<FieldKey, Set<AllocSite>> entry : fieldPts.entrySet()) {
                FieldKey key = entry.getKey();
                Set<AllocSite> sites = entry.getValue();
                AllocSite site = key.site;
                String siteStr = allocSiteStr(site);
                System.out.print("      " + siteStr + "." + key.field.getName() + " -> {");
                System.out.println(allocSiteSetStr(sites) + "}");
            }
        }

        Map<AllocSite, Set<Local>> revVarPts = state.revVarPts;
        if (!revVarPts.isEmpty()) {
            System.out.println("    Reverse (site -> variables):");
            for (Map.Entry<AllocSite, Set<Local>> entry : revVarPts.entrySet()) {
                AllocSite site = entry.getKey();
                Set<Local> locals = entry.getValue();
                System.out.print("      " + allocSiteStr(site) + " -> {");
                boolean first = true;
                for (Local l : locals) {
                    if (!first)
                        System.out.print(", ");
                    System.out.print(l.getName());
                    first = false;
                }
                System.out.println("}");
            }
        }

        Map<Local, Integer> lastWriteLine = state.lastWriteLine;
        if (!lastWriteLine.isEmpty()) {
            System.out.println("    Last write line (locals):");
            for (Map.Entry<Local, Integer> entry : lastWriteLine.entrySet()) {
                System.out.println("      " + entry.getKey().getName() + " @ line " + entry.getValue());
            }
        }
    }

    private static String allocSiteStr(AllocSite site) {
        if (site.unknown)
            return "UNKNOWN";
        return "AllocSite#" + site.id;
    }

    private static String allocSiteSetStr(Set<AllocSite> sites) {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (AllocSite s : sites) {
            if (!first)
                sb.append(", ");
            sb.append(allocSiteStr(s));
            first = false;
        }
        return sb.toString();
    }

    private static Set<AllocSite> setOf(AllocSite site) {
        Set<AllocSite> set = new HashSet<>();
        set.add(site);
        return set;
    }

    private static AllocSite getAllocSite(int line, Unit unit) {
        AllocSite site = totalAllocSites.get(line);
        if (site == null) {
            int id = unit.getJavaSourceStartLineNumber();
            site = new AllocSite(id, false, id);
            totalAllocSites.put(id, site);
        }
        return site;
    }

    static final class CallInvokeInfo {
        final int argIndex;
        final SootMethod containingMethod;

        CallInvokeInfo(int argIndex, SootMethod containingMethod) {
            this.argIndex = argIndex;
            this.containingMethod = containingMethod;
        }
    }

    private static final class AllocSite {
        private final int id;
        private final boolean unknown;
        private int lineNumber;

        AllocSite(int id, boolean unknown, int lineNumber) {
            this.id = id;
            this.unknown = unknown;
            this.lineNumber = lineNumber;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof AllocSite)) {
                return false;
            }
            AllocSite other = (AllocSite) obj;
            return id == other.id && unknown == other.unknown && lineNumber == other.lineNumber;
        }

        @Override
        public int hashCode() {
            return Objects.hash(id, unknown);
        }
    }

    private static final class FieldKey {
        private final AllocSite site;
        private final SootField field;

        private FieldKey(AllocSite site, SootField field) {
            this.site = site;
            this.field = field;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof FieldKey)) {
                return false;
            }
            FieldKey other = (FieldKey) obj;
            return Objects.equals(site, other.site) && Objects.equals(field, other.field);
        }

        @Override
        public int hashCode() {
            return Objects.hash(site, field);
        }
    }

    private static final class RedundantLoad {
        private final int line;
        private final String statement;
        private final String replacement;

        private RedundantLoad(int line, String statement, String replacement) {
            this.line = line;
            this.statement = statement;
            this.replacement = replacement;
        }
    }

    private static final class PointsToState {
        private final Map<Local, Set<AllocSite>> varPts;
        private final Map<FieldKey, Set<AllocSite>> fieldPts;
        private final Map<AllocSite, Set<Local>> revVarPts;
        private final Map<Local, Integer> lastWriteLine;

        private PointsToState() {
            this.varPts = new HashMap<>();
            this.fieldPts = new HashMap<>();
            this.revVarPts = new HashMap<>();
            this.lastWriteLine = new HashMap<>();
        }

        private static PointsToState empty() {
            return new PointsToState();
        }

        private PointsToState copy() {
            PointsToState copy = new PointsToState();
            for (Map.Entry<Local, Set<AllocSite>> entry : varPts.entrySet()) {
                copy.varPts.put(entry.getKey(), new HashSet<>(entry.getValue()));
            }
            for (Map.Entry<FieldKey, Set<AllocSite>> entry : fieldPts.entrySet()) {
                copy.fieldPts.put(entry.getKey(), new HashSet<>(entry.getValue()));
            }
            for (Map.Entry<AllocSite, Set<Local>> entry : revVarPts.entrySet()) {
                copy.revVarPts.put(entry.getKey(), new HashSet<>(entry.getValue()));
            }
            copy.lastWriteLine.putAll(lastWriteLine);
            return copy;
        }

        private PointsToState union(PointsToState other) {
            PointsToState result = new PointsToState();
            Set<Local> allLocals = new HashSet<>();
            allLocals.addAll(this.varPts.keySet());
            allLocals.addAll(other.varPts.keySet());
            for (Local local : allLocals) {
                Set<AllocSite> merged = new HashSet<>();
                Set<AllocSite> left = this.varPts.getOrDefault(local, setOf(UNKNOWN_ALLOC));
                Set<AllocSite> right = other.varPts.getOrDefault(local, setOf(UNKNOWN_ALLOC));
                merged.addAll(left);
                merged.addAll(right);
                result.setVar(local, merged);
            }

            Set<FieldKey> allFields = new HashSet<>();
            allFields.addAll(this.fieldPts.keySet());
            allFields.addAll(other.fieldPts.keySet());
            for (FieldKey key : allFields) {
                Set<AllocSite> merged = new HashSet<>();
                Set<AllocSite> left = this.fieldPts.getOrDefault(key, setOf(UNKNOWN_ALLOC));
                Set<AllocSite> right = other.fieldPts.getOrDefault(key, setOf(UNKNOWN_ALLOC));
                merged.addAll(left);
                merged.addAll(right);
                result.setField(key.site, key.field, merged);
            }

            Set<Local> allWriteLocals = new HashSet<>();
            allWriteLocals.addAll(this.lastWriteLine.keySet());
            allWriteLocals.addAll(other.lastWriteLine.keySet());
            for (Local local : allWriteLocals) {
                int leftLine = this.lastWriteLine.getOrDefault(local, Integer.MIN_VALUE);
                int rightLine = other.lastWriteLine.getOrDefault(local, Integer.MIN_VALUE);
                result.lastWriteLine.put(local, Math.max(leftLine, rightLine));
            }
            return result;
        }

        private Set<AllocSite> getVar(Local local) {
            return varPts.getOrDefault(local, setOf(UNKNOWN_ALLOC));
        }

        private void setVar(Local local, Set<AllocSite> sites) {
            Set<AllocSite> existing = varPts.get(local);
            if (existing != null) {
                for (AllocSite site : existing) {
                    Set<Local> locals = revVarPts.get(site);
                    if (locals != null) {
                        locals.remove(local);
                        if (locals.isEmpty()) {
                            revVarPts.remove(site);
                        }
                    }
                }
            }

            if (sites == null || sites.isEmpty()) {
                varPts.remove(local);
                return;
            }

            Set<AllocSite> newSites = new HashSet<>(sites);
            varPts.put(local, newSites);
            for (AllocSite site : newSites) {
                revVarPts.computeIfAbsent(site, k -> new HashSet<>()).add(local);
            }
        }

        private Set<Local> getLocalsForAlloc(AllocSite site) {
            return revVarPts.getOrDefault(site, Collections.emptySet());
        }

        private void recordWrite(Local local, int line) {
            lastWriteLine.put(local, line);
        }

        private int getLastWriteLine(Local local) {
            return lastWriteLine.getOrDefault(local, Integer.MAX_VALUE);
        }

        private Set<AllocSite> getField(AllocSite site, SootField field) {
            return fieldPts.getOrDefault(new FieldKey(site, field), Collections.emptySet());
        }

        private void setField(AllocSite site, SootField field, Set<AllocSite> sites) {
            if (sites == null || sites.isEmpty()) {
                fieldPts.remove(new FieldKey(site, field));
            } else {
                fieldPts.put(new FieldKey(site, field), new HashSet<>(sites));
            }
        }

        private void addField(AllocSite site, SootField field, Set<AllocSite> sites) {
            FieldKey key = new FieldKey(site, field);
            Set<AllocSite> existing = fieldPts.computeIfAbsent(key, k -> new HashSet<>());
            existing.addAll(sites);
        }

        private Set<SootField> getAllFields(AllocSite site) {
            Set<SootField> fields = new HashSet<>();
            for (FieldKey key : fieldPts.keySet()) {
                if (key.site.equals(site)) {
                    fields.add(key.field);
                }
            }
            return fields;
        }

        private void removeAllFields(AllocSite site) {
            List<FieldKey> toRemove = new ArrayList<>();
            for (FieldKey key : fieldPts.keySet()) {
                if (key.site.equals(site)) {
                    toRemove.add(key);
                }
            }
            for (FieldKey key : toRemove) {
                fieldPts.remove(key);
            }
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!(obj instanceof PointsToState)) {
                return false;
            }
            PointsToState other = (PointsToState) obj;
            return Objects.equals(varPts, other.varPts)
                    && Objects.equals(fieldPts, other.fieldPts)
                    && Objects.equals(revVarPts, other.revVarPts)
                    && Objects.equals(lastWriteLine, other.lastWriteLine);
        }

        @Override
        public int hashCode() {
            return Objects.hash(varPts, fieldPts, revVarPts, lastWriteLine);
        }
    }
}
