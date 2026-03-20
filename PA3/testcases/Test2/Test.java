class A {
    int x;
}

class B {
    A a;
    static B global;

    void foo(B b) {
        A p = new A(); //O10
        b.a = p;
        global = b;
        return;
    }
}

class Test {
    public static void main(String[] args) {
        A a = new A(); //O19
        B b = new B(); //O20
        b.a = a;
        b.foo(b);
    }
}