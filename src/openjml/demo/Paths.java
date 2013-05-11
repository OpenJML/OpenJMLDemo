package openjml.demo;

import java.io.FileNotFoundException;

public class Paths {
	
	//@ old boolean p1 = i < min;
	//@ {|
	//@   requires p1;
	//@   ensures \result == min;
	//@ also
	//@   requires i > max;
	//@   ensures \result == max;
	//@ also
	//@   requires !p1 && i <= max;
	//@   ensures \result == i;
	//@ |}
	public int clip(int i, int max, int min) {
		if (i < min) return min;
		if (i > max) return max;
		return i;
	}
	
	public void multipleErrors(int i) {
		if (i == 0) {
			//@ assert i > 0;
		} else {
			//@ assert i > 0;
		}
	}
	
	public void lotsOfPaths(int i) {
		int k = 0; int j = 1;
		switch (i) {
		default: k = i; break;
		case 1: k = 1;
		case 2: k = 2;
		case 3: k = 3;
		}
		//@ assert i == k;
		
		try {
			throw new Exception();
			//throw new RuntimeException();
			//throw new FileNotFoundException();
			//throw new NullPointerException();
		} catch (RuntimeException e) {
			j = 2;
		} catch (Exception e) {
			j = 3;
		} finally {
			i += k;
		}
		//@ assert i == 2*k;
	}
		
}
