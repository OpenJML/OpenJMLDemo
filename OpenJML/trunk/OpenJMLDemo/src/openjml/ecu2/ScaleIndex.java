
public class ScaleIndex {

	int intPart;
	int fracPart; // in perc 0..99
	int size;      // max integer index

	//@ invariant size > 0;	
	//@ invariant intPart >= 0 && intPart < size;
	//@ invariant intPart != size - 1 || fracPart == 0;
	//@ invariant fracPart >= 0;
	//@ invariant fracPart < 100;
	
	//@ model int linearScaler;
	//@ represents linearScaler = (this.intPart * 100 + this.fracPart) / this.size; 

	
	/*@ normal_behavior
	  @ requires fracPart >= 0;
	  @ requires fracPart < 100;
	  @ ensures this.intPart == intPart;
	  @ ensures this.fracPart == fracPart;
	  @ ensures this.size == size;
	  @ assignable this.intPart, this.fracPart, this.size;
	  @*/
	public ScaleIndex(int intPart, int fracPart, int size) {
		this.intPart = intPart;
		this.fracPart = fracPart;
		this.size = size;
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

	/*@ normal_behavior
	  @ ensures \result == size;
	  @ ensures \result > 0;
	  @*/
	public /*@ pure @*/ int getSize() {
		return size;
	}

}
