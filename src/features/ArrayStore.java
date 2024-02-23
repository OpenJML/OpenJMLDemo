package features;

public class ArrayStore {

    public static void main(String ... args) {
        try { test(); } catch (ArrayStoreException e) { System.out.println("EXCEPTION"); }
        try { test2(); } catch (ArrayStoreException e) { System.out.println("EXCEPTION2");}
    }

    //@ pure
    public static void test() {
        Object[] a = new Integer[10];
        a[0] = Boolean.TRUE;
    }

    //@ pure
    public static void test2() {
        Object[] a = new Integer[10];
        a[0] = true;  // Requires implicit conversion, which was a bug
    }
}
