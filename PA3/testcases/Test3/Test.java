class O {
    int x;
}

class A {
    O f;

    void func(O global) {
        O obj = new O();
        A a = new A();
        a.f = obj;
        global.x = 10;
    }
}

public class Test {
    static A global = new A();

    public static void main(String[] args) {
        A a = new A();
        // a.f = global;
        // a.func(global);
        global.f = new O();
        a.func(global.f);
    }
}
