import java.util.*;
import java.util.stream.Collectors;

import soot.*;

public class SimpleSceneTransform extends SceneTransformer {
    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        List<SootClass> classes = Scene.v().getApplicationClasses().stream()
                .sorted(Comparator.comparing(SootClass::getName))
                .collect(Collectors.toList());

        for (SootClass sc : classes) {
            System.out.println("CLASS " + sc.getName());

            List<SootClass> hier = getClassHierarchy(sc);

            System.out.println("FIELDS");
            int totalsize = 0;
            for (SootClass c : hier) {
                for (SootField sf : c.getFields()) {
                    if (sf.isStatic())
                        continue;
                    System.out.printf("%s::%s %s\n",
                            sf.getDeclaringClass().getName(),
                            sf.getType(),
                            sf.getName());

                    totalsize += get_fieldSize(sf.getType());
                }
            }
            totalsize += 12;
            if (sc.isAbstract())
                totalsize = 0;
            System.out.println("OBJECT SIZE " + totalsize);
            System.out.println("METHODS");

            Map<String, SootMethod> sMap = new LinkedHashMap<>();
            for (SootClass c : hier) {
                for (SootMethod sm : c.getMethods()) {
                    if (sm.isStatic())
                        continue;
                    String name = sm.getName();
                    if (name.equals("main") || name.equals("<init>"))
                        continue;
                    sMap.put(sm.getSubSignature(), sm);
                }
            }

            for (SootMethod sm : sMap.values()) {
                System.out.printf("%s::%s %s(%s)\n",
                        sm.getDeclaringClass().getName(),
                        sm.getReturnType(),
                        sm.getName(),
                        getParams(sm));
            }
            System.out.println("END CLASS\n");

        }
    }

    private List<SootClass> getClassHierarchy(SootClass sc) {
        List<SootClass> hier = new ArrayList<>();

        SootClass curr = sc;
        while (curr != null) {
            if (curr.getName().equals("java.lang.Object")) {
                break;
            }
            hier.add(curr);
            curr = curr.hasSuperclass() ? curr.getSuperclass() : null;
        }
        Collections.reverse(hier);
        return hier;
    }

    private int get_fieldSize(Type type) {
        if (type instanceof ArrayType || type instanceof RefType)
            return 4;
        if (type instanceof BooleanType || type instanceof ByteType)
            return 1;
        if (type instanceof CharType || type instanceof ShortType)
            return 2;
        if (type instanceof IntType || type instanceof FloatType)
            return 4;
        if (type instanceof LongType || type instanceof DoubleType)
            return 8;
        return 4;

    }

    private String getParams(SootMethod sm) {
        List<String> ty = new ArrayList<>();
        for (Type t : sm.getParameterTypes()) {
            ty.add(t.toString());
        }
        return String.join(", ", ty);
    }
}
