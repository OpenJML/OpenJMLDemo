package openjml.test;

public class Path2 {
	
	//@ invariant true;

	//@   requires c >= 'A' && c <= 'Z';
	//@   ensures \result >= 'a' && \result <= 'z';
	//@ also
	//@   requires c >= 'a' && c <= 'z';
	//@   ensures \result >= 'A' && \result <= 'Z';
	//@ also
	//@   requires !(c >= 'A' && c <= 'Z') && !(c >= 'a' && c <= 'z');
	//@   ensures \result == c;
	public char changeCase(char c) {
		char result = ' ';    
		if (c >= 'Z') {
			result = c;
		} else if (c >= 'A') {
			result =  (char)(c - 'A' + 'a');
		} else if (c > 'z') {
			result =  c;
		} else if (c > 'a') {
			result =  (char)(c - 'a' + 'A');
		} else {
			result = c;
		}
		return result;
	}
	 
	public void other(int i) {
		//@ assert i == 0;
	}
	
	static public class Y {}
}

class Z {}
