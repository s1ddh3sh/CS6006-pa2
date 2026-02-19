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
    class AbsObj {
        Unit allocSite;

        AbsObj(Unit u) {
            allocSite = u;
        }

        @Override
        public int hashCode() {
            return allocSite.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            return (obj instanceof AbsObj) && (((AbsObj) obj).allocSite == allocSite);
        }
    }

    class State {
        Map<Local, Set<AbsObj>> stack;
        Map<AbsObj, Map<SootField, Set<AbsObj>>> heap;

        State() {
            stack = new HashMap<>();
            heap = new HashMap<>();
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

    void join(State out, State in) {

        //stack
        for(Local l : in.stack.keySet()) {
            Set<AbsObj> inSet = in.stack.get(l);
            Set<AbsObj> outSet = out.stack.computeIfAbsent(l, k-> new HashSet<>());

            outSet.addAll(inSet);
        }

        //heap

        for(AbsObj o : in.heap.keySet()) {
            Map<SootField, Set<AbsObj>> inMap = in.heap.get(o);
            Map<SootField, Set<AbsObj>> outMap = out.heap.computeIfAbsent(o, k -> new HashSet<>());
            
            for(SootField f : inMap.keySet()) {
                Set<AbsObj> inSet = inMap.get(f);
                Set<AbsObj> outSet = outMap.computeIfAbsent(f, k-> new HashSet<>());

                outSet.addAll(inSet);
            }
        }
    }

    State dataFlow(Unit u, State in) {
        State out = in.deepCopy();

        if(u instanceof InvokeStmt || (u instanceof AssignStmt && ((AssignStmt)u).getRightOp() instanceof InvokeExpr)) {
            InvokeExpr ie = (u instanceof InvokeStmt) ? ((InvokeStmt)u).getInvokeExpr() : ((AssignStmt)u).getInvokeExpr();

            AbsObj top = new AbsObj(u);

            for(Map<SootField, Set<AbsObj>> fMap : out.heap.values()) {
                for(SootField f : fMap.keySet()) {
                    Set<AbsObj> topSet = new HashSet<>();
                    topSet.add(top);
                    fMap.put(f, topSet);
                }
            }

            if(u instanceof AssignStmt) {
                Value lhs = ((AssignStmt)u).getLeftOp();
                if(lhs instanceof Local) {
                    Set<AbsObj> st = new HashSet<>();
                    st.add(top);
                    out.stack.put((Local)lhs,st);
                }
            }
        }

        if(u instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) u;
            Value lhs = as.getLeftOp();
            Value rhs = as.getRightOp();


            // x = new Node()
            if(lhs instanceof Local && rhs instanceof NewExpr) {
                
            }
        }


        return out;
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

            List<String> results = new ArrayList<>();
            for (Unit u : g) {
                String r = redundant(u, IN.get(u), body);
                if (r != null)
                    results.add(r);
            }

        }
    }

}