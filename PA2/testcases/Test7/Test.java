public class Test {

    static class Node {
        Node next;
    }

    static Node global;

    public static void main(String[] args) {

        global = new Node();
        global.next = new Node();

        Node p = global.next;
        Node q = global.next;   // ✅ Redundant

    }
}
