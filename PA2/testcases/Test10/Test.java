class Node {
    Node f;
    Node g;
}

public class Test {
    public static void main(String[] args) {

        Node a = new Node();
        a.f = new Node();
        a.f.g = new Node();

        Node x = a.f.g;

        Node alias = a;
        alias.f.g = new Node();   // alias-based deep store

        Node y = a.f.g;           // ❌ NOT redundant

        a = new Node();           // base reassignment

        Node z = a.f.g;           // ❌ NOT redundant

    }
}
