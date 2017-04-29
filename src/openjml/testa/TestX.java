package openjml.testa;

public class TestX {

	// /*@ spec_public */
	private int apr;
	// /*@ spec_public */
	int apa;
	// /*@ spec_public */
	protected int apt;
	public int apb;
	
	/*@ pure */ private boolean mpr() { return true; }
	/*@ pure */  boolean mpa() { return true; }
	/*@ pure */ protected boolean mpt() { return true; }
}
