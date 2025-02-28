package features;

public class DivideByZero {

    public static void main(String ... args) {
        test(1);
        test(0);
    }

    public static int test(int i) {
        return 1/i;
    }

}
