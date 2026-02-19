
class Node {
    Node f;
    Node a;

    public void foo() {
        this.f = new Node();
    }
}

public class Test {

    public static void main(String[] args) {

        Node x = new Node();
        x.f = new Node();
        x.f.a = new Node();

        x.foo(); // <-- this causes loss of precision (⊤)

        Node p = x.f.a; // p = bottom
        Node q = x.f.a; // SHOULD NOT be marked redundant

    }
}
