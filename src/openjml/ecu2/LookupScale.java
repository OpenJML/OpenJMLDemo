
public class LookupScale {
	int[] values;

	//@ invariant this.values.length > 1;
	//@ invariant (\forall int k; k>0 && k<this.values.length; this.values[k-1] < this.values[k]);
	
	/*@ normal_behavior 
	  @ requires values.length > 1;
	  @ requires (\forall int k; k>0 && k<values.length; values[k-1] < values[k]);
	  @ ensures this.values == values;
	  @*/
	LookupScale(int[] values) {
		this.values = values;
	}
	
	/*@ normal_behavior 
	    requires size > 1;
	    requires min < max;
	    ensures this.values.length == size;
	    assignable this.values[*], this.values;
	  @*/
	LookupScale(int min, int max, int size) {
		this.values = new int[size];
		int chunk = (max-min) / (size - 1);
		//@ assume chunk > 0;
		this.values[0] = min;
		/*@ loop_invariant i>=1 && i<=this.values.length;
		    loop_invariant (\forall int k; k>0 && k<i; this.values[k-1] < this.values[k]);
		    decreases this.values.length - i;
		  @*/
		for(int i=1; i<this.values.length; i++) {
		  this.values[i] = this.values[i-1] + chunk;
		}
	}

	// TODO introduce mistake here
	/*@ normal_behavior
	  @ ensures \result.fracPart >= 0 && \result.fracPart < 100;
      @ ensures \result.intPart >= 0 && \result.intPart < this.values.length;
	  @ ensures \result.intPart == 0 || this.values[\result.intPart] <= sv.getValue();
	  @ ensures \result.intPart == this.values.length - 1 || sv.getValue() < this.values[\result.intPart+1];
	  @ ensures \result.size == this.values.length;
	  @*/ 
	public /*@ pure @*/ ScaleIndex lookupValue(SensorValue sv) {
		int v = sv.getValue();
		// First get the intPart
		// The most convenient way to lookup scales is from the end
		int intPart = this.values.length - 1;
		/*@ loop_invariant intPart>=-1;
		    loop_invariant intPart<this.values.length;
		  @*/
		while(intPart >= 0) {
			if(v >= this.values[intPart]) {
				break;
			}
			intPart--;
		}
		// MISTAKE HERE, can be -1
		// if(intPart < 0) intPart = 0;
		//@ assert intPart >= 0;
		int fracPart = 0;
		if(intPart == this.values.length - 1 || v < this.values[0]) {
			// Border cases
			//@ assert intPart == 0 || intPart == this.values.length-1;
			//@ assert fracPart == 0;
			return new ScaleIndex(intPart, fracPart, this.values.length);
		}
		// Then calculate the frac
		fracPart = (v - this.values[intPart]) * 100 / (this.values[intPart+1] - this.values[intPart]);
		//@ assert fracPart >= 0 && fracPart < 100;
        //@ assert intPart >= 0 && intPart < this.values.length;
		return new ScaleIndex(intPart, fracPart, this.values.length);
	}
	
}
