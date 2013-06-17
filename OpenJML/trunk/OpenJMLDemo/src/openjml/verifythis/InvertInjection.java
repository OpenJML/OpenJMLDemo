public class InvertInjection {

	static public int N;
	static public int M;
	static public int[] a;
	static public int[] b;
	
	//@ requires a != b; // Note - this is needed !
	//@ requires 0 <= N && N <= a.length;
	//@ requires 0 <= M && M <= b.length;
	//@ requires (\forall int i; 0<=i && i <N; 0<=a[i] && a[i]<M);
	//@ requires (\forall int i,j; 0<=i && i<j && j < N; a[i] != a[j]);
	//@ ensures (\forall int i; 0<=i && i < N; b[a[i]] == i);
	public void invert() {
		
		//@ loop_invariant 0<=k && k<=N;
		//@ loop_invariant (\forall int i; 0<=i && i < k; b[a[i]] == i);
		for (int k = 0; k < N; k++) {
			b[a[k]] = k;
		}
	}
	
}
