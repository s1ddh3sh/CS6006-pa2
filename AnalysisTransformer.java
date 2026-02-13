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
        public boolean equals(Object o) {
            return (o instanceof AbsObj) && ((AbsObj) o).allocSite == allocSite;
        }

        @Override
        public String toString() {
            return "Obj-" + allocSite.getJavaSourceStartLineNumber();
        }
    }

    class State {
        Map<Local, Set<AbsObj>> stack;
        Map<AbsObj, Map<SootField, Set<AbsObj>>> heap;

        Map<String, Local> available;

        State() {
            stack = new HashMap<>();
            heap  = new HashMap<>();
            available = new HashMap<>();

        }
        State deepCopy() {
            State copy = new State();

            // Copy Stack
            if(stack != null) {

                for (Map.Entry<Local, Set<AbsObj>> e : stack.entrySet()) {
                    Set<AbsObj> newSet = new HashSet<>(e.getValue());
                    copy.stack.put(e.getKey(), newSet);
                }
            }

            // Copy Heap
            if(heap != null) {

                for (Map.Entry<AbsObj, Map<SootField, Set<AbsObj>>> objEntry : heap.entrySet()) {
                    
                    Map<SootField, Set<AbsObj>> newFieldMap = new HashMap<>();
                    
                    for (Map.Entry<SootField, Set<AbsObj>> fieldEntry : objEntry.getValue().entrySet()) {
                        Set<AbsObj> newSet = new HashSet<>(fieldEntry.getValue());
                        newFieldMap.put(fieldEntry.getKey(), newSet);
                    }
                    
                    copy.heap.put(objEntry.getKey(), newFieldMap);
                }
            }
            copy.available.putAll(this.available);


            return copy;
        }

            @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();

            // -------- Stack --------
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

            // -------- Heap --------
            sb.append("HEAP:\n");
            if (heap.isEmpty()) {
                sb.append("  <empty>\n");
            } else {
                for (AbsObj obj : heap.keySet()) {
                    sb.append("  ").append(obj).append(" -> {\n");

                    Map<SootField, Set<AbsObj>> fieldMap = heap.get(obj);
                    if (fieldMap != null) {
                        for (SootField f : fieldMap.keySet()) {
                            sb.append("      ").append(f.getName()).append(" -> ");

                            Set<AbsObj> pts = fieldMap.get(f);
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
                    sb.append("  }\n");
                }
            }

            sb.append("AVAILABLE:\n");
            if (available.isEmpty()) {
                sb.append("  <empty>\n");
            } else {
                for (Map.Entry<String, Local> e : available.entrySet()) {
                    sb.append("  ")
                    .append(e.getKey())    
                    .append(" -> ")
                    .append(e.getValue()) 
                    .append("\n");
                }
            }
            // if (available.isEmpty()) {
            //     sb.append("  <empty>\n");
            // } else {
            //     for (String a : available) {
            //         sb.append("  ").append(a).append("\n");
            //     }
            // }
            return sb.toString();
        }
    }

    boolean joinIn(State target, State pre) {
        boolean changed = false;

        for (Local l : pre.stack.keySet()) {
            Set<AbsObj> inSet = pre.stack.get(l);
            Set<AbsObj> targetSet = target.stack.computeIfAbsent(l, k -> new HashSet<>());

            if (targetSet.addAll(inSet)) {
                changed = true;
            }
        }

        for (AbsObj obj : pre.heap.keySet()) {
            Map<SootField, Set<AbsObj>> inMap = pre.heap.get(obj);
            Map<SootField, Set<AbsObj>> targetMap = target.heap.computeIfAbsent(obj, k -> new HashMap<>());

            for (SootField f : inMap.keySet()) {
                Set<AbsObj> inSet = inMap.get(f);
                Set<AbsObj> targetSet = targetMap.computeIfAbsent(f, k -> new HashSet<>());

                if (targetSet.addAll(inSet)) {
                    changed = true;
                }
            }

        }

        for (Map.Entry<String, Local> e : pre.available.entrySet()) {
            String key = e.getKey();
            Local incoming = e.getValue();

            Local existing = target.available.get(key);

            if (existing == null) {
                target.available.put(key, incoming);
                changed = true;
            }
        }
        return changed;
    }

    boolean stateEquals(State a, State b) {
        return a.stack.equals(b.stack) && a.heap.equals(b.heap) && a.available.equals(b.available);
    }

    AbsObj getAbsObj(Unit u) {
        return new AbsObj(u);
    }

    State dataFlow(Unit u, State in) {
        State out = in.deepCopy();
        if (u instanceof InvokeStmt) {
            out.available.clear();
        }
        if(u instanceof AssignStmt) {
            AssignStmt as = (AssignStmt) u;
            Value lhs = as.getLeftOp();
            Value rhs = as.getRightOp();

            //x = new node;
            if(lhs instanceof Local && rhs instanceof NewExpr) {
                Local x = (Local) lhs;
                NewExpr y = (NewExpr) rhs;

                AbsObj obj = getAbsObj(u);

                Set<AbsObj> st = new HashSet<>();
                st.add(obj);
                out.stack.put(x, st);

                out.heap.computeIfAbsent(obj, k -> new HashMap<>());
            }

            //x=y;
            else if(lhs instanceof Local && rhs instanceof Local ) {
                Local x = (Local) lhs;
                Local y = (Local) rhs;

                Set<AbsObj> st = in.stack.getOrDefault(y, new HashSet<>());
                out.stack.put(x, new HashSet<>(st));
            }

            //x = y.f
            else if(lhs instanceof Local && rhs instanceof InstanceFieldRef) {
                Local x = (Local) lhs;
                InstanceFieldRef fieldRef = (InstanceFieldRef) rhs;

                Local base = (Local) fieldRef.getBase();
                SootField field = fieldRef.getField();

                Set<AbsObj> result = new HashSet<>();

                Set<AbsObj> base_st = in.stack.getOrDefault(base, new HashSet<>());

                for(AbsObj obj : base_st) {
                    Map<SootField, Set<AbsObj>> fieldMap = in.heap.get(obj);
                    if(fieldMap == null) continue;
                    
                    Set<AbsObj> field_st = fieldMap.get(field);
                    if(field_st != null) {
                        result.addAll(field_st);
                    }
                }
                out.stack.put(x, result);
                // if(!result.isEmpty()) {
                    for (AbsObj obj : base_st) {
                        String key = obj.toString() + "." + field.getName();
                        out.available.putIfAbsent(key, x);
                    }

                // }
            }
            else if (u instanceof InvokeStmt || rhs instanceof InvokeExpr) {
                out.available.clear();   // conservative kill
            }
            //x.f = y
            else if(lhs instanceof InstanceFieldRef && rhs instanceof Local) {
                InstanceFieldRef fr = (InstanceFieldRef) lhs;
                Local y = (Local) rhs;

                Local base = (Local) fr.getBase();
                SootField field = fr.getField();

                Set<AbsObj> base_st = in.stack.getOrDefault(base, new HashSet<>());
                Set<AbsObj> y_st = in.stack.getOrDefault(y, new HashSet<>());

                for(AbsObj obj : base_st) {
                    Map<SootField, Set<AbsObj>> fieldMap = out.heap.computeIfAbsent(obj, k -> new HashMap<>());

                    Set<AbsObj> fieldSet = fieldMap.computeIfAbsent(field, k -> new HashSet<>());

                    if(base_st.size() == 1) {
                        fieldSet.clear();
                        fieldSet.addAll(y_st);
                    }
                    else
                        fieldSet.addAll(y_st);
                }
                Set<String> toRemove = new HashSet<>();

                for (String a : out.available.keySet()) {
                    for (AbsObj obj : base_st) {
                        String prefix = obj.toString() + "." + field.getName();
                        if (a.equals(prefix)) {
                            toRemove.add(a);
                        }
                    }
                }

                for (String k : toRemove)
                    out.available.remove(k);

            }
            // x.f = const
            else if (lhs instanceof InstanceFieldRef && rhs instanceof Constant) {

                InstanceFieldRef fr = (InstanceFieldRef) lhs;
                Local base = (Local) fr.getBase();
                SootField field = fr.getField();

                Set<AbsObj> base_st = in.stack.getOrDefault(base, Collections.emptySet());

                for (AbsObj obj : base_st) {
                    Map<SootField, Set<AbsObj>> fmap =
                            out.heap.computeIfAbsent(obj, k -> new HashMap<>());

                    
                    Set<AbsObj> primVal = new HashSet<>();
                    primVal.add(new AbsObj(u)); 

                    fmap.put(field, primVal);
                }

                for (AbsObj obj : base_st) {
                    String key = obj.toString() + "." + field.getName();
                    out.available.remove(key);
                }
            }

        }
        return out;
    }

    String redundantCheck(Unit u, State in, Body body) {
        if (!(u instanceof AssignStmt)) return null;

        AssignStmt as = (AssignStmt) u;
        Value lhs = as.getLeftOp();
        Value rhs = as.getRightOp();

        if (!(rhs instanceof InstanceFieldRef))
            return null;

        Local x = (Local) lhs;
        InstanceFieldRef fr = (InstanceFieldRef) rhs;

        Local base = (Local) fr.getBase();
        SootField field = fr.getField();

        Set<AbsObj> loaded = new HashSet<>();

        Set<AbsObj> base_st = in.stack.getOrDefault(base, Collections.emptySet());

        for(AbsObj obj : base_st) {
            Map<SootField, Set<AbsObj>> fieldMap = in.heap.get(obj);
            if(fieldMap == null) continue;

            Set<AbsObj> field_st = fieldMap.get(field);
            if(field_st != null) {
                loaded.addAll(field_st);
            }
        }

        // if(loaded.isEmpty()) return null;
        
        Local replaceVar = null;

        for (AbsObj obj : base_st) {
            Map<SootField, Set<AbsObj>> fmap = in.heap.get(obj);
            if (fmap == null) continue;

            for (Map.Entry<SootField, Set<AbsObj>> e : fmap.entrySet()) {
                SootField otherField = e.getKey();
                Set<AbsObj> otherVal = e.getValue();

                if (!otherVal.equals(loaded))
                    continue;   // not value-equivalent

                String key = obj.toString() + "." + otherField.getName();

                if (in.available.containsKey(key)) {
                    replaceVar = in.available.get(key);  
                    break;
                }
            }
            if (replaceVar != null) break;
        }

        if (replaceVar == null || replaceVar.equals(x)) return null;

        String loadStr =
        base.getName() + ".<" +
        field.getDeclaringClass().getName() + ": " +
        field.getType() + " " +
        field.getName() + ">";

        return
        u.getJavaSourceStartLineNumber() + ":" +
        loadStr + " " +
        replaceVar.getName();
    }

    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {

        UnitGraph graph = new BriefUnitGraph(body);
        Chain<Unit> units = body.getUnits();
        Map<Unit, State> IN = new HashMap<>();
        Map<Unit, State> OUT = new HashMap<>();

        for (Unit u : graph) {
            IN.put(u, new State());
            OUT.put(u, new State());
        }

        Queue<Unit> worklist = new LinkedList<>(units);
        // worklist.addAll(graph.getHeads());

        while (!worklist.isEmpty()) {
            Unit u = worklist.poll();

            State newIn = new State();

            for (Unit pre : graph.getPredsOf(u)) {
                joinIn(newIn, OUT.get(pre));
            }
            if (!stateEquals(IN.get(u), newIn)) {
                IN.put(u, newIn);
            }

            State oldOut = OUT.get(u);
            State newOut = dataFlow(u, IN.get(u));

            if (!stateEquals(oldOut, newOut)) {

                OUT.put(u, newOut);

                for (Unit succ : graph.getSuccsOf(u)) {
                    worklist.add(succ);
                }
            }
        }
        List<String> results = new ArrayList<>();

        for (Unit u : graph) {
            String r = redundantCheck(u, IN.get(u), body);
            if (r != null) results.add(r);
        }

        // if (!results.isEmpty()) {
        //     System.out.println(
        //         body.getMethod().getDeclaringClass().getName() + ":" +
        //         body.getMethod().getName()
        //     );

        //     for (String s : results)
        //         System.out.println(s);
        // }
        for (Unit u : graph) { 
            System.out.println("================================="); 
            System.out.println("Unit: " + u); 
            System.out.println("----------- IN -----------"); 
            System.out.println(IN.get(u)); 
            System.out.println("----------- OUT ----------");
            System.out.println(OUT.get(u)); 
        }
    }
}