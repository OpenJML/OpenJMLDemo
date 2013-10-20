// package loops;

public class LoopExamples {

	private /*@ spec_public non_null */ int [] a;
	
	
	LoopExamples() {
		a = new int[5];
	}
	
	//@ requires a != null;
	public void setA(int [] a) {
		this.a = a;
	}
	
	/*@ normal_behavior
	    ensures \result == (\exists int i; 0 <= i && i < a.length; a[i] == x);
	 */
	/*@ pure*/ boolean contains(int x) {
		boolean found = false;
		//@ loop_invariant 0 <= i && i <= a.length;
        //@ loop_invariant found == (\exists int j; 0 <= j && j < i; a[j] == x);
		for (int i = 0; i < a.length; i++) {
			if (a[i] == x) {found = true;}
			else {}
		}
		return found;
	}
	

}
