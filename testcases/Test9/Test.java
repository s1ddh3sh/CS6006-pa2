public class Test {
  Test f;
  public static void main(String[] args) {
    Test a = new Test();
    a.f = new Test();
    a.f.f = new Test();
    Test b = a.f.f;
    Test c = a.f.f; // redundant?
  }
  public void foo(){

  }
}
