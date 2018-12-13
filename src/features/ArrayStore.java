package features;

public class ArrayStore {

	public static void main(String ... args) {
		try { test(); } catch (ArrayStoreException e) {}
		try { test2(); } catch (ArrayStoreException e) {}
	}
	
	public static void test() {
		Object[] a = new Integer[10];
		a[0] = new Boolean(true);
	}
	
	public static void test2() {
		Object[] a = new Integer[10];
		a[0] = true;  // Requires implicit conversion, which was a bug
	}
}
