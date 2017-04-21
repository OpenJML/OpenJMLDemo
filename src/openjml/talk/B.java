public class B {

  public static int j,k;

  //@ requires i > 0;
  //@ modifies j;
  //@ ensures j == i;
  public static void setj(int i) {
    k = i;
  }

  //@ ensures j == 1;
  public static void main(String[] args) {
    setj(0);
  }
}

