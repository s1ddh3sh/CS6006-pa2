/*class Node {
    Node f;
}

public class Test {

    static void foo(Node x) {

        Node p = x.f;
        Node q = x.f;   // ❌ NOT redundant (x is parameter)

    }

    public static void main(String[] args) {

        Node a = new Node();
        foo(a);

    }
}
*//* 

class Node {
    Node f;
}

public class Test {
     Test f ;
    static void foo(Node x) {

       // Node a = new Node();
       // a.f = new Node();
//
       // Node r1 = a.f;
       // Node r2 = a.f;   // ✅ Redundant (local allocation)
//
       // Node p = x.f;
       // Node q = x.f;   // ❌ NOT redundant (parameter)

        Test a = new Test();
        Test p = null;
        for(int i = 0; i < 100; i++) {
            p = a.f;  // stmt 7
        }




        

    }

    public static void main(String[] args) {

        Node n = new Node();
        foo(n);

    }
}
*/

/*
class Node {
    Node f;

    void bar() {

        Node p = this.f;
        Node q = this.f;   // ❌ NOT redundant

    }
}

public class Test {

    public static void main(String[] args) {

        Node a = new Node();
        a.bar();

    }
}
 */


/*
class Node {
    Node f;
}

public class Test {

    static void foo(Node x, Node y) {

        Node p = x.f;
        Node q = y.f;   // ❌ NOT redundant

    }

    public static void main(String[] args) {

        Node a = new Node();
        foo(a, a);

    }
}


*/


class A {
    void foo(int x) {
        if(this instanceof B) {
            B b = (B)this;
            b.setValue(x);
        }
    }
}

class B extends A {
    int f;

    void setValue(int x) { f = x; }
    int getValue() { return f; }
    void print() {
        System.out.println("f = " + f);
    }
}

class Main {
    public static void main(String[] args) {
        B b = new B();

        b.print();
        b.foo(5);
        b.print();
    }
}