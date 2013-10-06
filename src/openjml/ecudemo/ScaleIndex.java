
public class ScaleIndex {

	int intPart;
	int fracPart; // in perc 0..99

	//@ invariant fracPart >= 0;
	//@ invariant fracPart < 100;
	
	/*@ normal_behavior
	  @ requires fracPart >= 0;
	  @ requires fracPart < 100;
	  @ ensures this.intPart == intPart;
	  @ ensures this.fracPart == fracPart;
	  @ assignable this.intPart, this.fracPart;
	  @*/
	public ScaleIndex(int intPart, int fracPart) {
		this.intPart = intPart;
		this.fracPart = fracPart;
	}
	
	/*@ normal_behavior
	  @ ensures \result == intPart;
	  @*/
	public /*@ pure @*/ int getIntPart() {
		return intPart;
	}

	/*@ normal_behavior
	  @ ensures \result == fracPart;
	  @*/
	public /*@ pure @*/ int getFracPart() {
		return fracPart;
	}

}
