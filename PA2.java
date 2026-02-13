import soot.*;
import soot.options.Options;

public class PA2 {
    public static void main(String[] args) {
        String classpath = "./testcases/" + args[0];

        String[] sootArgs = {
                "-cp", classpath,
                "-pp",
                "-f", "J",
                "-t", "1",
                "-main-class", "Test",
                "-process-dir", classpath
        };

        AnalysisTransformer analysisTransformer = new AnalysisTransformer();
        PackManager.v().getPack("jtp").add(new Transform("jtp.dfa", analysisTransformer));
        Options.v().set_keep_line_number(true);

        soot.Main.main(sootArgs);

    }
}
