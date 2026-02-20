import java.util.*;
import soot.*;
import soot.util.Chain;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;

public class AnalysisTransformer extends BodyTransformer {
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
                        for (Iterator<AbsObj> it = pts.iterator(); it.hasNext();) {
                            sb.append(it.next()).append(" ");
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
                                for (Iterator<AbsObj> it = pts.iterator(); it.hasNext();) {
                                    sb.append(it.next()).append(" ");
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
    }

    class PointsToAnalysis extends ForwardFlowAnalysis<Unit, State> {

        PointsToAnalysis(UnitGraph graph) {
            super(graph);
            doAnalysis();
        }

        @Override
        protected State newInitialFlow() {
            return new State(); // empty stack + heap
        }

        @Override
        protected State entryInitialFlow() {
            return new State(); // entry = empty
        }

        @Override
        protected void copy(State src, State dst) {
            dst.stack.clear();
            dst.heap.clear();

            for (var e : src.stack.entrySet()) {
                dst.stack.put(e.getKey(), new HashSet<>(e.getValue()));
            }

            for (var e : src.heap.entrySet()) {
                Map<SootField, Set<AbsObj>> fMap = new HashMap<>();
                for (var f : e.getValue().entrySet()) {
                    fMap.put(f.getKey(), new HashSet<>(f.getValue()));
                }
                dst.heap.put(e.getKey(), fMap);
            }
        }

        @Override
        protected void merge(State in1, State in2, State out) {
            out.stack.clear();
            out.heap.clear();

            // Stack
            for (Local l : in1.stack.keySet()) {
                Set<AbsObj> out_st = new HashSet<>(in1.stack.get(l));
                out_st.addAll(in2.stack.getOrDefault(l, new HashSet<>()));
                out.stack.put(l, out_st);
            }

            for (Local l : in2.stack.keySet()) {
                if (!(out.stack.containsKey(l))) {
                    out.stack.put(l, new HashSet<>(in2.stack.get(l)));
                }
            }

            // Heap
            for (AbsObj obj : in1.heap.keySet()) {
                Map<SootField, Set<AbsObj>> fmap = new HashMap<>();

                Map<SootField, Set<AbsObj>> m1 = in1.heap.get(obj);
                Map<SootField, Set<AbsObj>> m2 = in2.heap.get(obj);

                if (m1 != null) {
                    for (var f1 : m1.entrySet()) {
                        fmap.put(f1.getKey(), new HashSet<>(f1.getValue()));
                    }
                }
                if (m2 != null) {
                    for (var f2 : m2.entrySet()) {
                        fmap.computeIfAbsent(f2.getKey(), k -> new HashSet<>()).addAll(f2.getValue());
                    }
                }
                out.heap.put(obj, fmap);
            }

        }

        @Override
        protected void flowThrough(State in, Unit u, State out) {
            copy(in, out);

            if (!(u instanceof AssignStmt))
                return;

            AssignStmt as = (AssignStmt) u;
            Value lhs = as.getLeftOp();
            Value rhs = as.getRightOp();

            // x= new node
            if (lhs instanceof Local && rhs instanceof NewExpr) {
                Local x = (Local) lhs;
                AbsObj obj = new AbsObj(u);

                Set<AbsObj> st = new HashSet<>();
                st.add(obj);

                out.stack.put(x, st);
                out.heap.put(obj, new HashMap<>());
            }

            // x = y
            if (lhs instanceof Local && rhs instanceof Local) {
                Local x = (Local) lhs;
                Local y = (Local) rhs;

                out.stack.put(x, new HashSet<>(in.stack.getOrDefault(y, Set.of())));
            }

            // x = y.f
            if (lhs instanceof Local && rhs instanceof InstanceFieldRef) {
                Local x = (Local) lhs;
                InstanceFieldRef fr = (InstanceFieldRef) rhs;
                Local base = (Local) fr.getBase();
                SootField field = fr.getField();

                Set<AbsObj> res = new HashSet<>();

                for (AbsObj obj : in.stack.getOrDefault(base, Set.of())) {
                    Map<SootField, Set<AbsObj>> fMap = in.heap.get(obj);
                    res.addAll(fMap.getOrDefault(field, Set.of()));
                }
                out.stack.put(x, res);

            }

            // x.f = y
            if (lhs instanceof InstanceFieldRef && rhs instanceof Local) {
                Local y = (Local) rhs;
                InstanceFieldRef fr = (InstanceFieldRef) lhs;
                Local base = (Local) fr.getBase();
                SootField field = fr.getField();

                Set<AbsObj> base_objs = in.stack.getOrDefault(base, Set.of());
                for (AbsObj obj : base_objs) {
                    Map<SootField, Set<AbsObj>> fMap = out.heap.computeIfAbsent(obj, k -> new HashMap<>());

                    fMap.put(field, new HashSet<>(in.stack.getOrDefault(y, Set.of())));

                }
            }
        }
    }

    @Override
    public void internalTransform(Body body, String phaseName, Map<String, String> options) {
        UnitGraph graph = new BriefUnitGraph(body);
        PointsToAnalysis pta = new PointsToAnalysis(graph);

        for (Unit u : graph) {
            State in = pta.getFlowBefore(u);
            State out = pta.getFlowAfter(u);

            System.out.println("=================================");
            System.out.println("Unit: " + u);
            System.out.println("----------- IN -----------");
            System.out.println(in);
            System.out.println("----------- OUT ----------");
            System.out.println(out);
        }
    }
}
