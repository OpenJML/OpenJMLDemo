package openjml.test;


public class Path {

	//@ requires i > 0;
	//@ ensures \result == i;
	//@ also 
	//@ requires i <= 0;
	//@ ensures \result == 1; 
	public int m(int i) {
		@org.jmlspecs.annotation.NonNull Object o;
		int result = 0;
		if (i > 0) {
			result = i;
		}
		return result;
	}
	
	public int n(int j) {
		int k = 5;
		int d = m(j);
		int p = k / d;
		return p;
	}
}
