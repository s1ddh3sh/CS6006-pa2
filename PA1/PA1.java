import soot.PackManager;
import soot.Transform;

public class PA1 {
    public static void main(String[] args) {
        String classpath = "./testcases/";

        String[] sootArgs = {
                "-cp", classpath,
                "-pp",
                "-f", "J",
                "-w",
                "-main-class", "Test",
                "-process-dir", classpath
        };

        SimpleSceneTransform pass = new SimpleSceneTransform();
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.idfa", pass));
        // Options.v().set_keep_line_number(true);

        soot.Main.main(sootArgs);
        // AnalysisTransformer.printResults();

    }
}

