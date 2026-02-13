public class Test {
    static class Node {
        Node f1;
    }

    public static void main(String[] args) {
        Node a = new Node();

        if (args.length > 0) {
            Node x = a.f1;
        }

        Node z = a.f1; // NOT redundant
        Node y = a.f1; // Redundant
    }
}
