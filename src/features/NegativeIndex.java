package features;

public class NegativeIndex {
    
    static public int[] array = new int[10];
    
    //@ static public invariant array != null && array.length == 10;

    public static void main(String ... args) {
        test(0);
        test(-1);
    }
    //@requires i < 10;
    public static int test(int i) {
        return array[i];
    }

}
