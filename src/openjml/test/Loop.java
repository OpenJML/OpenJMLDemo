package openjml.test;

public class Loop {

	//@ requires a != null;
	public void m(int[] a) {
		int[] b = new int[10];
		//@ loop_invariant 0<=i && i<=a.length && (\forall int k; 0<=k && k < i; b[i] == a[i]);
		for (int i=0; i<a.length; i++) {
			b[i] = a[i];
		}
	}
}
