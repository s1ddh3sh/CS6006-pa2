class O {
    int x;
}

class A {
    O f;

    void func() {
        O obj = new O();
        A a = new A();
        a.f = obj;
    }
}

public class Test {
    public static void main(String[] args) {
        
    }
}
