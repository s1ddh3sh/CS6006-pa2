import java.util.*;
import soot.*;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;


public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;


    @Override
    public void internalTransform(String phaseName, Map<String, String> options) {
        cg = Scene.v().getCallGraph();

        var entryPoints = Scene.v().getEntryPoints();

        assert(entryPoints.size() == 1);
        SootMethod entryMethod = entryPoints.get(0);

        handleMainMethod(entryMethod);
    }

    void handleMainMethod(SootMethod myMethod) {
        Body body = myMethod.getActiveBody();

        for(Unit u : body.getUnits()) {
            Stmt stmt = (Stmt) u;
            int lineNumber = stmt.getJavaSourceStartLineNumber();

            if(stmt.containsInvokeExpr()) {
                System.out.println("Call site found: " + stmt + "@" + lineNumber);
                Iterator<Edge> targets = cg.edgesOutOf(stmt);
                while(targets.hasNext()) {
                    Edge edge = targets.next();
                    SootMethod targMethod = edge.tgt();
                    System.out.println("Potential target: " + targMethod.getSignature());
                }
            }
        }
    }
}