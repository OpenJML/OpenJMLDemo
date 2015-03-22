package features;

public class ArrayStore {

	public static void main(String ... args) {
		test();
	}
	
	public static void test() {
		Object[] a = new Integer[10];
		a[0] = new Boolean(true);
	}
	
	public static void test2() {
		Object[] a = new Integer[10];
		a[0] = true;  // Makes an internal exception
	}
}
