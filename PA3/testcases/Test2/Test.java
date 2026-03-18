class A {
    int x;
}

class B {
    A a;
    static B global;

    void foo(B b) {
        A p = new A(); 
        b.a = p;
        global = b;
        return;
    }
}

class Test {
    public static void main(String[] args) {
        A a = new A(); 
        B b = new B(); 
        b.a = a;
        b.foo(b);
    }
}