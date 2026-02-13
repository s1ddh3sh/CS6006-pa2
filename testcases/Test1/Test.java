class Node {
    Node f1;
    Node f2;
    Node g;
    Node() {}
}

public class Test {
    public static void main(String[] args) {
        Node a = new Node();
        a.f1 = new Node();
        Node b = new Node();
        b.f1 = new Node();
        a.f2 = new Node();
        Node c = a.f1;
        a.f2 = a.f1;
        b.f1 = a.f2;
    }
}