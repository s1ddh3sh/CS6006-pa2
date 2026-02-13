class A {
    public A f1;
}

public class Test {
    public static void main(String[] args) {
        A a, b, x, y;
        a = new A();
        b = new A();

        a.f1 = new A();
        if(a == b) {
            x = a.f1;
        } else {
            x = a.f1;
        }

        A z = a.f1;     // is this Redundant?
    }
}