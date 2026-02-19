import java.util.*;
import soot.*;
import soot.util.Chain;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;

public class AnalysisTransformer extends BodyTransformer {

    static Map<String, List<String>> allResults = new TreeMap<>();

    public static void printResults() {

        for (String key : allResults.keySet()) {

            System.out.println(key);

            List<String> lines = allResults.get(key);

            Collections.sort(lines, (a, b) -> {
                int la = Integer.parseInt(a.split(":")[0]);
                int lb = Integer.parseInt(b.split(":")[0]);
                return Integer.compare(la, lb);
            });

            for (String l : lines)
                System.out.println(l);
        }
    }

    class AbsObj {
        Unit allocSite;

        AbsObj(Unit u) {
            allocSite = u;
        }

        @Override
        public int hashCode() {
            return allocSite == null ? 0 : allocSite.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            return (obj instanceof AbsObj) && (((AbsObj) obj).allocSite == allocSite);
        }

        @Override
        public String toString() {
            if (allocSite == null)
                return "TOP";
            return "Obj-" + allocSite.getJavaSourceStartLineNumber();
        }
    }

    final AbsObj TOP = new AbsObj(null);

    class State {
        Map<Local, Set<AbsObj>> stack;
        Map<AbsObj, Map<SootField, Set<AbsObj>>> heap;

        State() {
            stack = new HashMap<>();
            heap = new HashMap<>();
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();

            sb.append("STACK:\n");
            if (stack.isEmpty()) {
                sb.append("  <empty>\n");
            } else {
                for (Local l : stack.keySet()) {
                    sb.append("  ").append(l.getName()).append(" -> ");

                    Set<AbsObj> pts = stack.get(l);
                    if (pts == null || pts.isEmpty()) {
                        sb.append("{}\n");
                    } else {
                        sb.append("{ ");
                        for (AbsObj o : pts) {
                            sb.append(o).append(" ");
                        }
                        sb.append("}\n");
                    }
                }
            }
            sb.append("HEAP:\n");

            if (heap.isEmpty()) {
                sb.append("  <empty>\n");
            } else {
                for (AbsObj o : heap.keySet()) {
                    sb.append("  ").append(o).append(" -> {\n");

                    Map<SootField, Set<AbsObj>> fMap = heap.get(o);
                    if (fMap != null) {
                        for (SootField f : fMap.keySet()) {
                            sb.append("      ").append(f.getName()).append(" -> ");

                            Set<AbsObj> pts = fMap.get(f);
                            if (pts == null || pts.isEmpty()) {
                                sb.append("{}\n");
                            } else {
                                sb.append("{ ");
                                for (AbsObj ob : pts) {
                                    sb.append(ob).append(" ");
                                }
                                sb.append("}\n");
                            }
                        }
                    }
                    sb.append("  }\n");

                }
            }
            return sb.toString();
        }

        State deepCopy() {
            State out = new State();

            if (stack != null) {
                for (Map.Entry<Local, Set<AbsObj>> e : stack.entrySet()) {
                    Set<AbsObj> newSet = new HashSet<>(e.getValue());
                    out.stack.put(e.getKey(), newSet);
                }
            }
            if (heap != null) {
                for (Map.Entry<AbsObj, Map<SootField, Set<AbsObj>>> objEntry : heap.entrySet()) {

                    Map<SootField, Set<AbsObj>> newFieldMap = new HashMap<>();

                    for (Map.Entry<SootField, Set<AbsObj>> fieldEntry : objEntry.getValue().entrySet()) {
                        Set<AbsObj> newSet = new HashSet<>(fieldEntry.getValue());
                        newFieldMap.put(fieldEntry.getKey(), newSet);
                    }

                    out.heap.put(objEntry.getKey(), newFieldMap);
                }
            }
            return out;
        }
    }

    boolean stateEquals(State a, State b) {
        return a.stack.equals(b.stack) && a.heap.equals(b.heap);
    }

    AbsObj getAbsObj(Unit u) {
        return new AbsObj(u);
    }

    void join(State out, State in) {

        // stack
        for (Local l : in.stack.keySet()) {
            Set<AbsObj> inSet = in.stack.get(l);
            Set<AbsObj> outSet = out.stack.computeIfAbsent(l, k -> new HashSet<>());

            outSet.addAll(inSet);
        }

        // heap

        for (AbsObj o : in.heap.keySet()) {
            Map<SootField, Set<AbsObj>> inMap = in.heap.get(o);
            Map<SootField, Set<AbsObj>> outMap = out.heap.computeIfAbsent(o, k -> new HashMap<>());

            for (SootField f : inMap.keySet()) {
                Set<AbsObj> inSet = inMap.get(f);
                Set<AbsObj> outSet = outMap.computeIfAbsent(f, k -> new HashSet<>());

                outSet.addAll(inSet);
            }
        }
    }

    State dataFlow(Unit u, State in) {
        State out = in.deepCopy();

        if (u instanceof InvokeStmt
                || (u instanceof AssignStmt && ((AssignStmt) u).getRightOp() instanceof InvokeExpr)) {
            InvokeExpr ie = (u instanceof InvokeStmt) ? ((InvokeStmt) u).getInvokeExpr()
                    : ((AssignStmt) u).getInvokeExpr();
            
            SootMethod m = ie.getMethod();
            // AbsObj top = new AbsObj(u);
            if (m.getName().equals("<init>"))
                return out;

            for (Map<SootField, Set<AbsObj>> fMap : out.heap.values()) {
                for (SootField f : fMap.keySet()) {
                    Set<AbsObj> topSet = new HashSet<>();
                    topSet.add(TOP);
                    fMap.put(f, topSet);
                }
            }

            Map<SootField, Set<AbsObj>> topMap = out.heap.computeIfAbsent(TOP, k -> new HashMap<>());

            if (u instanceof AssignStmt) {
                Value lhs = ((AssignStmt) u).getLeftOp();
                if (lhs instanceof Local) {
                    Set<AbsObj> st = new HashSet<>();
                    st.add(TOP);
                    out.stack.put((Local) lhs, st);
                }
            }
        }

        if (u instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) u;
            Value lhs = as.getLeftOp();
            Value rhs = as.getRightOp();

            // x = new Node()
            if (lhs instanceof Local && rhs instanceof NewExpr) {
                Local x = (Local) lhs;

                Set<AbsObj> outSet = new HashSet<>();
                AbsObj o = getAbsObj(u);
                outSet.add(o);
                out.stack.put(x, outSet);
                out.heap.computeIfAbsent(o, k -> new HashMap<>());
            }

            // x = y;
            if (lhs instanceof Local && rhs instanceof Local) {
                Local x = (Local) lhs;
                Local y = (Local) rhs;

                Set<AbsObj> st = in.stack.getOrDefault(y, new HashSet<>());
                out.stack.put(x, st);
            }

            // x = y.f
            if (lhs instanceof Local && rhs instanceof InstanceFieldRef) {
                Local x = (Local) lhs;
                InstanceFieldRef fieldRef = (InstanceFieldRef) rhs;

                SootField field = fieldRef.getField();
                Local y = (Local) fieldRef.getBase();

                Set<AbsObj> result = new HashSet<>();
                Set<AbsObj> y_objs = in.stack.getOrDefault(y, new HashSet<>());

                for (AbsObj obj : y_objs) {
                    Map<SootField, Set<AbsObj>> fMap = in.heap.get(obj);
                    if (obj == TOP) {
                        result.add(TOP);
                        continue;
                    }
                    if (fMap == null)
                        continue;
                    Set<AbsObj> f_objs = fMap.get(field);
                    if (f_objs != null)
                        result.addAll(f_objs);
                }
                out.stack.put(x, result);

            }
            // x.f = y
            if (lhs instanceof InstanceFieldRef && rhs instanceof Local) {
                Local y = (Local) rhs;
                InstanceFieldRef fieldRef = (InstanceFieldRef) lhs;

                Local x = (Local) fieldRef.getBase();
                SootField field = fieldRef.getField();

                Set<AbsObj> x_objs = in.stack.getOrDefault(x, new HashSet<>());
                Set<AbsObj> y_objs = in.stack.getOrDefault(y, new HashSet<>());

                for (AbsObj obj : x_objs) {
                    Map<SootField, Set<AbsObj>> fMap = out.heap.computeIfAbsent(obj, k -> new HashMap<>());
                    Set<AbsObj> fSet = fMap.computeIfAbsent(field, k -> new HashSet<>());
                    if (x_objs.size() == 1) {
                        fSet.clear();
                        fSet.addAll(y_objs);
                    } else {
                        fSet.addAll(y_objs);
                    }
                }
            }

            // x.f = const
            if (lhs instanceof InstanceFieldRef && rhs instanceof Constant) {

                InstanceFieldRef fr = (InstanceFieldRef) lhs;
                Local x = (Local) fr.getBase();
                SootField field = fr.getField();

                Set<AbsObj> x_objs = in.stack.getOrDefault(x, new HashSet<>());

                for (AbsObj obj : x_objs) {
                    Map<SootField, Set<AbsObj>> fMap = out.heap.computeIfAbsent(obj, k -> new HashMap<>());
                    Set<AbsObj> primit_st = new HashSet<>();
                    primit_st.add(new AbsObj(u));
                    fMap.put(field, primit_st);
                }
            }
        }

        return out;
    }

    String redundant(Unit u, State in, Body body) {
        if (!(u instanceof AssignStmt))
            return null;

        AssignStmt as = (AssignStmt) u;
        Value lhs = as.getLeftOp();
        Value rhs = as.getRightOp();

        if (!(rhs instanceof InstanceFieldRef))
            return null;

        Local x = (Local) lhs;
        InstanceFieldRef fr = (InstanceFieldRef) rhs;

        Local y = (Local) fr.getBase();
        SootField field = fr.getField();
        Set<AbsObj> loaded = new HashSet<>();

        Set<AbsObj> y_objs = in.stack.getOrDefault(y, new HashSet<>());

        for (AbsObj obj : y_objs) {
            if(obj == TOP) {
                loaded.add(TOP);
                continue;
            }
            Map<SootField, Set<AbsObj>> fMap = in.heap.get(obj);
            if (fMap == null)
                continue;
            Set<AbsObj> fSet = fMap.get(field);
            if (fSet != null)
                loaded.addAll(fSet);

        }

        // if (loaded.isEmpty())
        //     return null;

        Local replaceVar = null;
        for (Map.Entry<Local, Set<AbsObj>> e : in.stack.entrySet()) {
            Local v = e.getKey();
            if (v.equals(x))
                continue;
            if (v.getName().startsWith("$"))
                continue;

            if (e.getValue().equals(loaded)) {
                replaceVar = v;
                break;
            }
        }

        if (replaceVar == null)
            return null;

        String res = u.getJavaSourceStartLineNumber() + ":" + as.toString() + " " + replaceVar.getName();

        return res;

    }

    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {

        UnitGraph g = new BriefUnitGraph(body);
        Chain<Unit> units = body.getUnits();
        Map<Unit, State> IN = new HashMap<>();
        Map<Unit, State> OUT = new HashMap<>();

        for (Unit u : g) {
            IN.put(u, new State());
            OUT.put(u, new State());
        }

        Queue<Unit> worklist = new LinkedList<>(units);
        List<String> results = new ArrayList<>();
        while (!worklist.isEmpty()) {
            Unit u = worklist.poll();

            State newIn = new State();

            for (Unit pre : g.getPredsOf(u)) {
                join(newIn, OUT.get(pre));
            }

            if (!stateEquals(newIn, IN.get(u))) {
                IN.put(u, newIn);
            }

            State oldOut = OUT.get(u);
            State newOut = dataFlow(u, IN.get(u));

            if (!stateEquals(oldOut, newOut)) {
                OUT.put(u, newOut);
                for (Unit sc : g.getSuccsOf(u)) {
                    worklist.add(sc);
                }
            }

        }
        for (Unit unit : g) {
            String r = redundant(unit, IN.get(unit), body);
            if (r != null)
                results.add(r);
        }

        if (!results.isEmpty()) {
            String key = body.getMethod().getDeclaringClass().getName() + ":" + body.getMethod().getName();

            allResults.putIfAbsent(key, new ArrayList<>());
            allResults.get(key).addAll(results);
        }
        for (Unit u : g) {
            System.out.println("=================================");
            System.out.println("Unit: " + u);
            System.out.println("----------- IN -----------");
            System.out.println(IN.get(u));
            System.out.println("----------- OUT ----------");
            System.out.println(OUT.get(u));
        }
    }

}