
public class LookupTable1d {

	LookupScale scaleX;
	
	int[] lookupValues; // does not have to be sorted
	
	//@ invariant lookupValues.length == scaleX.values.length;
	
    /*@ normal_behavior
	  @ requires lookupValues.length > 1;
	  @ requires scale.values.length == lookupValues.length;
	  @ ensures this.scaleX == scale;
	  @ ensures this.lookupValues == lookupValues;
	  @ assignable this.lookupValues, this.scaleX;
	  @*/
	public LookupTable1d(LookupScale scale, int[] lookupValues) {
		this.scaleX = scale;
		this.lookupValues = lookupValues;
	}
	
	public /*@ pure @*/ int getValue(SensorValue sv) {
		ScaleIndex si = scaleX.lookupValue(sv);
		int i = si.getIntPart();
		int f = si.getFracPart();
		int v = lookupValues[i];
		if(i<lookupValues.length-1) {
			int vn = lookupValues[i+1];
			v = v + (vn - v)*f/100; // calculate in the fraction part
			// MISTAKE HERE
			// v = v + f;
		}
		//@ assert v >= lookupValues[i];
		//@ assert i == lookupValues.length - 1 || v <= lookupValues[i+1];
		return v;
	}
}
