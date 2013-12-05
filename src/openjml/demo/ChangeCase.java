//package openjml.demo;

public class ChangeCase {
	
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
		if (c >= 'z') {
			result = c;
		} else if (c >= 'a') {
			result =  (char)(c - 'a' + 'A');
		} else if (c >= 'Z') {
			result =  c;
		} else if (c >= 'A') {
			result =  (char)(c - 'A' + 'a');
		} else {
			result = c;
		}
		return result;
	}

}
