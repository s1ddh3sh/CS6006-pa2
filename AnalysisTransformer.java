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
            return allocSite.hashCode();
        }

        @Override
        public boolean equals(Object o) {
            return (o instanceof AbsObj) && ((AbsObj) o).allocSite == allocSite;
        }

        @Override
        public String toString() {
            if (allocSite == null) return "TOP";
            return "Obj-" + allocSite.getJavaSourceStartLineNumber();
        }
    }
    final AbsObj TOP = new AbsObj(null);

    class State {
        Map<Local, Set<AbsObj>> stack;
        Map<AbsObj, Map<SootField, Set<AbsObj>>> heap;

        Map<SootField, Set<AbsObj>> statics;


        State() {
            stack = new HashMap<>();
            heap  = new HashMap<>();
            statics = new HashMap<>();
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
            for (Map.Entry<SootField, Set<AbsObj>> e : statics.entrySet()) {
                copy.statics.put(e.getKey(), new HashSet<>(e.getValue()));
            }

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

            sb.append("STATIC:\n"); 
                if(statics.isEmpty()) {
                    sb.append("  <empty>\n");

                }else {
                    for (SootField l : statics.keySet()) {
                    sb.append("  ").append(l.getName()).append(" -> ");

                    Set<AbsObj> pts = statics.get(l);
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

        for (SootField f : pre.statics.keySet()) {
            Set<AbsObj> inSet = pre.statics.get(f);
            Set<AbsObj> targetSet = target.statics.computeIfAbsent(f, k -> new HashSet<>());
            if (targetSet.addAll(inSet)) changed = true;
        }
        return changed;
    }

    boolean stateEquals(State a, State b) {
        return a.stack.equals(b.stack) && a.heap.equals(b.heap);
    }

    AbsObj getAbsObj(Unit u) {
        return new AbsObj(u);
    }

    State dataFlow(Unit u, State in) {
        State out = in.deepCopy();
        if (u instanceof InvokeStmt ||
        (u instanceof AssignStmt && ((AssignStmt) u).getRightOp() instanceof InvokeExpr)) {

             InvokeExpr ie = (u instanceof InvokeStmt)
                ? ((InvokeStmt)u).getInvokeExpr()
                : ((AssignStmt)u).getInvokeExpr();

            SootMethod m = ie.getMethod();

            // Ignore constructors
            if (m.getName().equals("<init>"))
                return out;
            
            for (Map<SootField, Set<AbsObj>> fmap : out.heap.values()) {
                for (Map.Entry<SootField, Set<AbsObj>> e : fmap.entrySet()) {

                    Set<AbsObj> fresh = new HashSet<>();
                    fresh.add(new AbsObj(u));   // new version after call
                    e.setValue(fresh);
                }
            }
            return out;
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

                
            }
            // global = x
            else if (lhs instanceof StaticFieldRef && rhs instanceof Local) {
                StaticFieldRef sfr = (StaticFieldRef) lhs;
                SootField f = sfr.getField();
                Set<AbsObj> val = in.stack.getOrDefault((Local) rhs, new HashSet<>());
                out.statics.put(f, new HashSet<>(val));
            }
            // x = global
            else if (lhs instanceof Local && rhs instanceof StaticFieldRef) {
                Local x = (Local) lhs;
                StaticFieldRef sfr = (StaticFieldRef) rhs;
                SootField f = sfr.getField();
                Set<AbsObj> val = in.statics.getOrDefault(f, new HashSet<>());
                out.stack.put(x, new HashSet<>(val));
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

        if(loaded.isEmpty()) return null;
        
        Local replaceVar = null;

        for (Map.Entry<Local, Set<AbsObj>> e : in.stack.entrySet()) {
            Local v = e.getKey();

            if (v.equals(x)) continue;
            if (v.getName().startsWith("$")) continue;

            if (e.getValue().equals(loaded)) {
                replaceVar = v;
                break;
            }
        }

        if (replaceVar == null) return null;

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

        if (!results.isEmpty()) {
            String key =
                body.getMethod().getDeclaringClass().getName() + ":" +
                body.getMethod().getName();

            allResults.putIfAbsent(key, new ArrayList<>());
            allResults.get(key).addAll(results);
        }

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