package features;

public class IllegalArgument {

    public static void main(String ... args) {
        test();
    }

    //@ pure
    public static void test() {
        //@ check \elemtype(\type(Object)) == \type(boolean);
    }

}
