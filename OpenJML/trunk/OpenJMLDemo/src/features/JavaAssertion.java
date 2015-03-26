package features;

public class JavaAssertion {

	public static void main(String ... args) {
		test(-1);
	}
	
	public static void test(int i) {
		System.out.println("BEFORE");
		assert i >= 0;
		System.out.println("AFTER");
	}
	
}
