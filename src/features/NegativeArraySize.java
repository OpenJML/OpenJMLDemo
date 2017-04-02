package features;

public class NegativeArraySize {

	public static void main(String ... args) {
		test(1);
		test(0);
		test(-1);
	}
	
	public static int[] test(int size) {
		int[] a = new int[size];
		return a;
	}
}
