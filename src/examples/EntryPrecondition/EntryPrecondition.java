
public class EntryPrecondition {
	//@ requires i > 0;
	static public void m(int i) {
		System.out.println("m() called with " + i);
		n(i);
	}
	
	//@ requires i > 1;
	static public void n(int i) {
		System.out.println("n() called with " + i);
	}
}
