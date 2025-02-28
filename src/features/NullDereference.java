package features;

public class NullDereference {
    
    int i = 42;

    public static void main(String ... args) {
        test(new NullDereference());
        test(null);
    }

    public static int test(/*@ nullable */ NullDereference n) {
        return n.i;
    }

}
