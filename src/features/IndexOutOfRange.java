package features;

public class IndexOutOfRange {
    
    static public int[] array = new int[10];
    
    //@ static public invariant array != null && array.length == 10;

    public static void main(String ... args) {
        test(0);
        test(10);
    }
    //@ requires i >= 0;
    public static int test(int i) {
        return array[i];
    }

}
