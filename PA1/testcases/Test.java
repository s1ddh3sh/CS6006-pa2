public class Test {
    public static void main(String[] args) {
        // Entry point for Soot
    }
}

class A {
    public int a1;
    public int a2;
    static public int a3;

    public static void staticFoo() {
        // This is a static method
    }
}

class B extends A {
    static public int b1;

    public static void staticBar() {
        // This is a static method
    }
}

class C extends B {
    public int c1;
    static public int c2;

    public static void staticBar() {
        // This shadows or overloads the static method name from B
    }
}