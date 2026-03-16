
import java.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.parser.node.ALabelName;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;

    private static final AllocSite UNKNOWN_ALLOC = new AllocSite(-1, null, null, true);

    private static final Map<Unit, AllocSite> allocSites = new HashMap<>();

    private static final Map<Integer, AllocSite> allocSiteObjs = new HashMap<>();

    private static final Map<String, Map<Unit, PointsToState>> methodPtsIn = new HashMap<>();

    private static final Map<Integer, List<CallInvokeInfo>> passedToCalls = new HashMap<>();

    private static final Map<Integer, EscapeStatus> escapeStatus = new HashMap<>();

    private static final Map<Integer, Set<Integer>> rewriteLines = new HashMap<>();
    private static int nextAllocId = 0;

    enum EscapeStatus {
        LOCAL, REWRITE, ESCAPED
    }

    @Override
    public void internalTransform(String phaseName, Map<String, String> options) {
        cg = Scene.v().getCallGraph();
        for (SootClass cls : Scene.v().getApplicationClasses()) {

            for (SootMethod method : cls.getMethods()) {
                
                if (!shouldAnalyze(method))
                    continue;

                Body body = method.retrieveActiveBody();
                // System.out.println("\nFor method : " + method.getDeclaringClass().getName() +
                // method.getName());
                UnitGraph graph = new BriefUnitGraph(body);
                Map<Unit, Integer> unitToIndex = buildUnitToIndex(body);
                for (Unit u : body.getUnits()) {
                    if (u instanceof AssignStmt) {
                        AssignStmt stmt = (AssignStmt) u;
                        if (stmt.getRightOp() instanceof AnyNewExpr) {
                            int id = nextAllocId++;
                            AllocSite site = new AllocSite(id, u, method, false);
                            allocSites.put(u, site);
                            allocSiteObjs.put(id, site);
                            escapeStatus.put(id, EscapeStatus.LOCAL);
                            rewriteLines.put(id, new TreeSet<>());
                        }
                    }
                }
                Map<Unit, PointsToState> ptsIn = new HashMap<>();
                Map<Unit, PointsToState> ptsOut = new HashMap<>();
                runPointsToAnalysis(graph, unitToIndex, ptsIn, ptsOut);

                methodPtsIn.put(method.getSignature(), ptsIn);

            }
        }

        for (SootClass cls : Scene.v().getApplicationClasses()) {
            for (SootMethod method : cls.getMethods()) {
                if (!shouldAnalyze(method))
                    continue;
                objectUsage(method);
            }
        }

        // analyzeCallsAndPropagate();
        // printResults();

    }

    void objectUsage(SootMethod method) {
        Body body = method.retrieveActiveBody();

        Map<Unit, PointsToState> ptsIn = methodPtsIn.get(method.getSignature());

        if (ptsIn == null)
            return;

        for (Unit u : body.getUnits()) {
            PointsToState state = ptsIn.get(u);
            if (state == null)
                continue;

            if (!(u instanceof Stmt))
                continue;

            Stmt stmt = (Stmt) u;

            if (stmt instanceof ReturnStmt) {
                Value retVal = ((ReturnStmt) stmt).getOp();
                if (retVal instanceof Local) {
                    markEscape((Local) retVal, state);
                }
                continue;
            }

            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value lhs = assign.getLeftOp();
                Value rhs = assign.getRightOp();

                if (lhs instanceof StaticFieldRef && rhs instanceof Local) {
                    markEscape((Local) rhs, state);
                }

                if (lhs instanceof InstanceFieldRef && rhs instanceof Local) {
                    Local base = (Local) ((InstanceFieldRef) lhs).getBase();
                    Local value = (Local) rhs;
                    Set<AllocSite> basePts = state.getVar(base);

                    if (basePts.contains(UNKNOWN_ALLOC)) {
                        markEscape(value, state);
                    }
                }
            }

            if (stmt.containsInvokeExpr()) {
                InvokeExpr invoke = stmt.getInvokeExpr();
                List<Value> args = invoke.getArgs();

                // for args
                for (int i = 0; i < args.size(); i++) {
                    Value arg = args.get(i);
                    if (!(arg instanceof Local))
                        continue;

                    Set<AllocSite> argPts = state.getVar((Local) arg);
                    for (AllocSite site : argPts) {
                        if (site.unknown)
                            continue;
                        passedToCalls
                                .computeIfAbsent(site.id, k -> new ArrayList<>())
                                .add(new CallInvokeInfo(u, i, method));
                    }
                }

                // for receiver
                if (invoke instanceof InstanceInvokeExpr) {
                    Value base = ((InstanceInvokeExpr) invoke).getBase();

                    if (base instanceof Local) {
                        Set<AllocSite> basePts = state.getVar((Local) base);
                        for (AllocSite site : basePts) {
                            if (site.unknown)
                                continue;
                            passedToCalls
                                    .computeIfAbsent(site.id, k -> new ArrayList<>())
                                    .add(new CallInvokeInfo(u, -1, method));
                        }
                    }
                }

            }
        }
    }

    private void markEscape(Local local, PointsToState state) {
        Set<AllocSite> pts = state.getVar(local);
        for (AllocSite site : pts) {
            if (!site.unknown) {
                escapeStatus.put(site.id, EscapeStatus.ESCAPED);
            }
        }
    }

    private void analyzeCallsAndPropagate() {
        for (Map.Entry<Integer, List<CallInvokeInfo>> entry : passedToCalls.entrySet()) {
            int id = entry.getKey();
            System.out.println("\nSiteId : " + id + "\n");

            System.out.println("CallSites : \n");
            for (CallInvokeInfo info : entry.getValue()) {
                System.out.println(info.callUnit);
                System.out.println(info.argIndex);
                System.out.println(info.containingMethod.getName());
                System.out.println("\n");
            }
        }

        for (Map.Entry<Integer, Set<Integer>> entry : rewriteLines.entrySet()) {
            int id = entry.getKey();
            System.out.println("\nSiteId : " + id + "\n");

            System.out.println("RewriteLines:\n");
            System.out.println(entry.getValue());
        }
        for (Map.Entry<Integer, List<CallInvokeInfo>> entry : passedToCalls.entrySet()) {
            int id = entry.getKey();
            if (escapeStatus.get(id) == EscapeStatus.ESCAPED)
                continue;

            for (CallInvokeInfo info : entry.getValue()) {
                boolean escapes = resolveCall(id, info);
                if (escapes) {
                    escapeStatus.put(id, EscapeStatus.ESCAPED);
                    break;
                }
            }
        }

        // propagate the escape status
        Deque<Integer> worklist = new ArrayDeque<>();
        for (Map.Entry<Integer, EscapeStatus> e : escapeStatus.entrySet()) {
            if (e.getValue() == EscapeStatus.ESCAPED) {
                worklist.add(e.getKey());
            }
        }

        while (!worklist.isEmpty()) {
            int siteId = worklist.poll();
            AllocSite site = allocSiteObjs.get(siteId);

            if (site == null)
                continue;

            Map<Unit, PointsToState> ptsIn = methodPtsIn.get(site.method.getSignature());
            if (ptsIn == null)
                continue;

            PointsToState state = ptsIn.get(site.unit);

            if (state == null)
                continue;

            AllocSite allocSite = getAllocSiteObj(siteId);
            if (allocSite == null)
                continue;

            for (SootField field : state.getAllFields(allocSite)) {
                for (AllocSite reachable : state.getField(allocSite, field)) {
                    if (reachable.unknown)
                        continue;

                    if (escapeStatus.get(reachable.id) != EscapeStatus.ESCAPED) {
                        escapeStatus.put(reachable.id, EscapeStatus.ESCAPED);
                        worklist.add(reachable.id);
                    }
                }
            }
        }

    }

    enum CalleeStatus {
        READS_ONLY, WRITES_FIELD, RETURNS_ARG, PASSES_FURTHER
    }

    private boolean resolveCall(int siteId, CallInvokeInfo record) {

        Iterator<Edge> edges = cg.edgesOutOf(record.callUnit);

        if (!edges.hasNext())
            return true;

        Set<Integer> lines = new TreeSet<>();

        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod target = edge.tgt();

            if (target.getDeclaringClass().isLibraryClass())
                return true;

            CalleeStatus status = resolveCallee(target, record.argIndex);

            switch (status) {
                case WRITES_FIELD:
                case RETURNS_ARG:
                    return true;

                case READS_ONLY:
                    lines.add(record.callUnit.getJavaSourceStartLineNumber());
                    break;

                case PASSES_FURTHER:
                    List<CallInvokeInfo> innerCallSites = findInnerCallSites(target, record.argIndex);

                    for (CallInvokeInfo inner : innerCallSites) {
                        boolean innerEscapes = resolveCall(siteId, inner);
                        if (innerEscapes)
                            return true;
                    }

                    rewriteLines.get(siteId).add(
                            record.callUnit.getJavaSourceStartLineNumber());
                    break;

            }
        }

        rewriteLines.get(siteId).addAll(lines);
        escapeStatus.put(siteId, EscapeStatus.REWRITE);
        return false;
    }

    private List<CallInvokeInfo> findInnerCallSites(SootMethod method, int argIndex) {
        List<CallInvokeInfo> result = new ArrayList<>();
        if (!method.isConcrete())
            return result;

        Body body = method.retrieveActiveBody();

        Local param = getParamLocal(body, argIndex);
        if (param == null)
            return result;

        for (Unit u : body.getUnits()) {
            if (!(u instanceof Stmt))
                continue;
            Stmt stmt = (Stmt) u;
            if (!stmt.containsInvokeExpr())
                continue;

            InvokeExpr invoke = stmt.getInvokeExpr();

            List<Value> args = invoke.getArgs();
            for (int i = 0; i < args.size(); i++) {
                if (args.get(i).equals(param)) {
                    result.add(new CallInvokeInfo(u, i, method));
                }
            }

            if (invoke instanceof InstanceInvokeExpr) {
                Value base = ((InstanceInvokeExpr) invoke).getBase();
                if (base.equals(param)) {
                    result.add(new CallInvokeInfo(u, -1, method));
                }
            }
        }
        return result;
    }

    private Local getParamLocal(Body body, int argIndex) {
        Local param = null;

        if (argIndex == -1) {
            for (Unit u : body.getUnits()) {
                if (u instanceof IdentityStmt) {
                    IdentityStmt id = (IdentityStmt) u;
                    if (id.getRightOp() instanceof ThisRef) {
                        param = (Local) id.getLeftOp();
                        break;
                    }
                }
            }
        } else {
            for (Unit u : body.getUnits()) {
                if (u instanceof IdentityStmt) {
                    IdentityStmt id = (IdentityStmt) u;
                    if (id.getRightOp() instanceof ParameterRef) {
                        ParameterRef pr = (ParameterRef) id.getRightOp();
                        if (pr.getIndex() == argIndex) {
                            param = (Local) id.getLeftOp();
                            break;
                        }
                    }
                }
            }
        }
        return param;
    }

    private CalleeStatus resolveCallee(SootMethod method, int argIndex) {
        if (!method.isConcrete())
            return CalleeStatus.PASSES_FURTHER;

        Body body = method.retrieveActiveBody();

        Local param = getParamLocal(body, argIndex);

        if (param == null)
            return CalleeStatus.READS_ONLY;

        for (Unit u : body.getUnits()) {
            if (!(u instanceof Stmt))
                continue;
            Stmt stmt = (Stmt) u;

            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value lhs = assign.getLeftOp();
                Value rhs = assign.getRightOp();

                if (lhs instanceof InstanceFieldRef) {
                    Local base = (Local) ((InstanceFieldRef) lhs).getBase();
                    if (base.equals(param))
                        return CalleeStatus.WRITES_FIELD;
                }

                if (lhs instanceof InstanceFieldRef && rhs instanceof Local) {
                    if (((Local) rhs).equals(param))
                        return CalleeStatus.WRITES_FIELD;
                }

            }

            if (stmt instanceof ReturnStmt) {
                Value ret = ((ReturnStmt) stmt).getOp();
                if (ret instanceof Local && ret.equals(param)) {
                    return CalleeStatus.RETURNS_ARG;
                }
            }

            if (stmt.containsInvokeExpr()) {
                InvokeExpr invoke = stmt.getInvokeExpr();
                for (Value arg : invoke.getArgs()) {
                    if (arg instanceof Local && arg.equals(param)) {
                        return CalleeStatus.PASSES_FURTHER;
                    }
                }

                if (invoke instanceof InstanceInvokeExpr) {
                    Value base = ((InstanceInvokeExpr) invoke).getBase();
                    if (base instanceof Local && base.equals(param)) {
                        return CalleeStatus.PASSES_FURTHER;
                    }
                }
            }
        }

        return CalleeStatus.READS_ONLY;
    }

    private void printResults() {
        for (Map.Entry<Integer, AllocSite> entry : allocSiteObjs.entrySet()) {
            int siteId = entry.getKey();
            AllocSite info = entry.getValue();
            EscapeStatus status = escapeStatus.getOrDefault(siteId, EscapeStatus.LOCAL);

            String prefix = "O" + info.lineNumber + " = ";

            if (status == EscapeStatus.ESCAPED) {
                System.out.println(prefix + "N");
            } else {
                Set<Integer> lines = rewriteLines.getOrDefault(siteId, Collections.emptySet());
                if (lines.isEmpty()) {
                    System.out.println(prefix + "Y[]");
                } else {
                    System.out.println(prefix + "Y" + lines.toString()
                            .replace(" ", ""));
                }
            }
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
        return !"<init>".equals(name) && !"<clinit>".equals(name);
    }

    private static Map<Unit, Integer> buildUnitToIndex(Body body) {
        Map<Unit, Integer> map = new HashMap<>();
        int index = 0;
        for (Unit u : body.getUnits()) {
            map.put(u, index++);
        }
        return map;
    }

    private static void runPointsToAnalysis(
            UnitGraph graph,
            Map<Unit, Integer> unitToIndex,
            Map<Unit, PointsToState> inMap,
            Map<Unit, PointsToState> outMap) {
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
            PointsToState outState = transferPointsTo(unit, inState, unitToIndex);
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

    private static void processInvokeExpr(PointsToState state, InvokeExpr invokeExpr) {
        Queue<AllocSite> queue = new ArrayDeque<>();

        if (invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr instanceInvoke = (InstanceInvokeExpr) invokeExpr;
            Value base = instanceInvoke.getBase();
            if (base instanceof Local) {
                Set<AllocSite> basePts = state.getVar((Local) base);
                for (AllocSite site : basePts) {
                    if (!site.equals(UNKNOWN_ALLOC)) {
                        queue.add(site);
                    }
                }
            }
        }

        for (Value arg : invokeExpr.getArgs()) {
            if (arg instanceof Local) {
                Set<AllocSite> argPts = state.getVar((Local) arg);
                for (AllocSite site : argPts) {
                    if (!site.equals(UNKNOWN_ALLOC)) {
                        queue.add(site);
                    }
                }
            }
        }

        Set<AllocSite> processed = new HashSet<>();
        while (!queue.isEmpty()) {
            AllocSite site = queue.poll();
            if (processed.contains(site)) {
                continue;
            }
            processed.add(site);

            Map<SootField, Set<AllocSite>> fieldsToProcess = new HashMap<>();
            Set<SootField> fields = state.getAllFields(site);
            for (SootField field : fields) {
                Set<AllocSite> fieldPts = state.getField(site, field);
                if (!fieldPts.isEmpty()) {
                    fieldsToProcess.put(field, new HashSet<>(fieldPts));
                }
            }

            state.removeAllFields(site);

            for (Map.Entry<SootField, Set<AllocSite>> entry : fieldsToProcess.entrySet()) {
                for (AllocSite targetSite : entry.getValue()) {
                    if (!targetSite.equals(UNKNOWN_ALLOC) && !processed.contains(targetSite)) {
                        queue.add(targetSite);
                    }
                }
            }
        }
    }

    private static PointsToState transferPointsTo(
            Unit unit, PointsToState inState, Map<Unit, Integer> unitToIndex) {
        PointsToState outState = inState.copy();
        int currentIndex = unitToIndex.getOrDefault(unit, Integer.MAX_VALUE);
        if (unit instanceof IdentityStmt) {
            return outState;
        }

        if (unit instanceof InvokeStmt) {
            InvokeStmt invokeStmt = (InvokeStmt) unit;
            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
            processInvokeExpr(outState, invokeExpr);
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
            processInvokeExpr(outState, invokeExpr);

            if (lhs instanceof Local) {
                Local left = (Local) lhs;
                SootMethod method = invokeExpr.getMethod();
                Type returnType = method.getReturnType();
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

    // void handleMainMethod(SootMethod myMethod) {
    // Body body = myMethod.getActiveBody();

    // for (Unit u : body.getUnits()) {
    // Stmt stmt = (Stmt) u;
    // int lineNumber = stmt.getJavaSourceStartLineNumber();

    // if (stmt.containsInvokeExpr()) {
    // System.out.println("Call site found: " + stmt + "@" + lineNumber);
    // Iterator<Edge> targets = cg.edgesOutOf(stmt);
    // while (targets.hasNext()) {
    // Edge edge = targets.next();
    // SootMethod targMethod = edge.tgt();
    // System.out.println("Potential target: " + targMethod.getSignature());
    // }
    // }
    // }
    // }
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

    private static AllocSite getAllocSite(Unit unit, Map<Unit, Integer> unitToIndex) {
        AllocSite site = allocSites.get(unit);
        if (site == null) {
            int id = nextAllocId++;
            site = new AllocSite(id, unit, null, false);
            allocSites.put(unit, site);
            allocSiteObjs.put(id, site);
        }
        return site;
    }

    private static AllocSite getAllocSiteObj(int siteId) {
        AllocSite site = allocSiteObjs.get(siteId);
        return site;
    }

    private static final class AllocSite {
        private final int id;
        private final Unit unit;
        private final SootMethod method;
        private final boolean unknown;

        private int lineNumber;

        AllocSite(int id, Unit unit, SootMethod method, boolean unknown) {
            this.id = id;
            this.unit = unit;
            this.method = method;
            this.unknown = unknown;
            this.lineNumber = -1;
            if (unit != null)
                this.lineNumber = unit.getJavaSourceStartLineNumber();
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
            return id == other.id && lineNumber == other.lineNumber && unknown == other.unknown;
        }

        @Override
        public int hashCode() {
            return Objects.hash(id, lineNumber);
        }
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