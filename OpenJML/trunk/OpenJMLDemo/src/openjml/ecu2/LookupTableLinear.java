
public class LookupTableLinear {

	int startValue;
	int range;
	//@ invariant range > 0;
	
	//@ model int endValue;
	//@ represents endValue = this.startValue + range;
	//@ invariant endValue > startValue;
	
	/*@ normal_behavior
	  @   requires range > 0;
	  @   ensures this.startValue == startValue;
	  @   ensures this.range == range;
	  @   assignable this.startValue, this.range;
	  @*/
	public LookupTableLinear(int startValue, int range) {
		this.startValue = startValue;
		this.range = range;
	}
	
    /*@ normal_behavior
	  @ ensures \result == startValue +(range * si.linearScaler) / 100;
	  @*/ 
	public /*@ pure @*/ int getValue(ScaleIndex si) {
		int result = this.startValue + (range * ((si.getIntPart()*100 + si.getFracPart())/si.getSize())) / 100;
		//@ assert result >= this.startValue;
		//@ assert result <= this.endValue;
		return result;
	}
}
