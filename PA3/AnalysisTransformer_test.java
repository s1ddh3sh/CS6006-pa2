import java.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.toolkits.graph.*;
import soot.jimple.toolkits.callgraph.Edge;

public class AnalysisTransformer_test extends SceneTransformer {
    static CallGraph cg;
    private static final AllocSite UNKNOWN_ALLOC = new AllocSite(-1, null, true);
    // private static boolean initialized = false;
    private static final Map<String, Map<String, List<RedundantLoad>>> RESULTS = new TreeMap<>();
    private static final Map<Unit, AllocSite> allocSiteByUnit = new HashMap<>();
    private static final Map<AllocSite, List<CallInvokeInfo>> passedToCalls = new HashMap<>();

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        cg = Scene.v().getCallGraph();

        var entryPoints = Scene.v().getEntryPoints();

        assert (entryPoints.size() == 1);
        SootMethod entryMethod = entryPoints.get(0);

        analyzeMethod(entryMethod);
    }

    // }
    void analyzeMethod(SootMethod method) {

        Body body = method.retrieveActiveBody();

        UnitGraph graph = new BriefUnitGraph(body);
        Map<Unit, Integer> unitToIndex = buildUnitToIndex(body);
        Map<Unit, PointsToState> ptsIn = new HashMap<>();
        Map<Unit, PointsToState> ptsOut = new HashMap<>();
        runPointsToAnalysis(graph, unitToIndex, ptsIn, ptsOut, method);
    }

    private static boolean shouldAnalyze(SootMethod method) {
        if (method == null || !method.isConcrete() || method.isPhantom()) {
            return false;
        }
        if (method.getDeclaringClass().isLibraryClass()) {
            return false;
        }
        String name = method.getName();
        return !"<init>".equals(name) && !"<clinit>".equals(name);
    }

    private static Map<Unit, Integer> buildUnitToIndex(Body body) {
        Map<Unit, Integer> map = new HashMap<>();
        // int index = 0;
        for (Unit u : body.getUnits()) {
            map.put(u, u.getJavaSourceStartLineNumber());
        }
        return map;
    }

    private static void runPointsToAnalysis(
            UnitGraph graph,
            Map<Unit, Integer> unitToIndex,
            Map<Unit, PointsToState> inMap,
            Map<Unit, PointsToState> outMap, SootMethod method) {
        for (Unit unit : graph) {
            inMap.put(unit, PointsToState.empty());
            outMap.put(unit, PointsToState.empty());
        }

        Deque<Unit> worklist = new ArrayDeque<>();
        Set<Unit> visited = new HashSet<>();
        for (Unit unit : graph) {
            worklist.add(unit);
        }

        while (!worklist.isEmpty()) {
            Unit unit = worklist.removeFirst();
            PointsToState inState = mergePointsTo(graph.getPredsOf(unit), outMap, visited);
            PointsToState outState = transferPointsTo(unit, inState, unitToIndex, method);
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

    private static void processInvokeExpr(PointsToState state, InvokeExpr invokeExpr, Unit callUnit,
            SootMethod method) {
        // Queue<AllocSite> queue = new ArrayDeque<>();

        // receiver
        if (invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr instanceInvoke = (InstanceInvokeExpr) invokeExpr;
            Value base = instanceInvoke.getBase();
            if (base instanceof Local) {
                Set<AllocSite> basePts = state.getVar((Local) base);
                for (AllocSite site : basePts) {
                    passedToCalls.computeIfAbsent(site, k -> new ArrayList<>())
                            .add(new CallInvokeInfo(callUnit, -1, method));
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
                    passedToCalls.computeIfAbsent(site, k -> new ArrayList<>())
                            .add(new CallInvokeInfo(callUnit, i, method));
                }
            }
        }

    }

    private static PointsToState transferPointsTo(
            Unit unit, PointsToState inState, Map<Unit, Integer> unitToIndex, SootMethod method) {
        PointsToState outState = inState.copy();
        int currentIndex = unitToIndex.getOrDefault(unit, unit.getJavaSourceStartLineNumber());
        if (unit instanceof IdentityStmt) {
            return outState;
        }

        if (unit instanceof InvokeStmt) {
            InvokeStmt invokeStmt = (InvokeStmt) unit;
            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
            processInvokeExpr(outState, invokeExpr, unit, method);
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
            processInvokeExpr(outState, invokeExpr, unit, method);

            if (lhs instanceof Local) {
                Local left = (Local) lhs;
                SootMethod met = invokeExpr.getMethod();
                Type returnType = met.getReturnType();
                if (!(returnType instanceof VoidType)) {
                }
                outState.recordWrite(left, currentIndex);
            }
            return outState;
        }

        if (lhs instanceof Local) {
            Local left = (Local) lhs;
            if (rhs instanceof AnyNewExpr) {
                outState.setVar(left, setOf(getAllocSite(unit, unitToIndex)));
            } else if (rhs instanceof Local) {
                outState.setVar(left, outState.getVar((Local) rhs));
            } else if (rhs instanceof StaticFieldRef) {
                outState.setVar(left, setOf(UNKNOWN_ALLOC));
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
            outState.recordWrite(left, currentIndex);
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
                rhsPts = setOf(getAllocSite(unit, unitToIndex));
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

    private static void printResults() {
        for (Map.Entry<String, Map<String, List<RedundantLoad>>> classEntry : RESULTS.entrySet()) {
            String className = classEntry.getKey();
            for (Map.Entry<String, List<RedundantLoad>> methodEntry : classEntry.getValue().entrySet()) {
                List<RedundantLoad> loads = methodEntry.getValue();
                if (loads.isEmpty()) {
                    continue;
                }
                String methodSubSig = methodEntry.getKey();
                String methodName = methodSubSig;
                int spaceIdx = methodSubSig.indexOf(' ');
                int parenIdx = methodSubSig.indexOf('(');
                if (spaceIdx != -1 && parenIdx != -1 && spaceIdx < parenIdx) {
                    methodName = methodSubSig.substring(spaceIdx + 1, parenIdx);
                } else if (parenIdx != -1) {
                    methodName = methodSubSig.substring(0, parenIdx);
                }

                System.out.print(className + ":");
                System.out.println(methodName);
                for (RedundantLoad load : loads) {
                    System.out.println(
                            ""
                                    + load.line
                                    + ":"
                                    + load.statement
                                    + " "
                                    + load.replacement);
                }
            }
        }
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

    private static AllocSite getAllocSite(Unit unit, Map<Unit, Integer> unitToIndex) {
        AllocSite site = allocSiteByUnit.get(unit);
        if (site == null) {
            int id = unitToIndex.get(unit);
            site = new AllocSite(id, unit, false);
            allocSiteByUnit.put(unit, site);
        }
        return site;
    }

    static final class CallInvokeInfo {
        final Unit callUnit;
        final int argIndex;
        final SootMethod containingMethod;

        CallInvokeInfo(Unit callUnit, int argIndex, SootMethod containingMethod) {
            this.callUnit = callUnit;
            this.argIndex = argIndex;
            this.containingMethod = containingMethod;
        }
    }

    private static final class AllocSite {
        private final int id;
        private final Unit unit;
        private final boolean unknown;

        AllocSite(int id, Unit unit, boolean unknown) {
            this.id = id;
            this.unit = unit;
            this.unknown = unknown;
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
            return id == other.id && unknown == other.unknown;
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
