
public class LookupTable1d {

	LookupScale scaleHorizontal;
	
	int[] lookupValues; // does not have to be sorted
	
	//@ invariant lookupValues.length == scaleHorizontal.values.length;
	
    /*@ normal_behavior
	  @ requires lookupValues.length > 1;
	  @ requires scale.values.length == lookupValues.length;
	  @ ensures this.scaleHorizontal == scale;
	  @ ensures this.lookupValues == lookupValues;
	  @ assignable \nothing;
	  @*/
	public LookupTable1d(LookupScale scale, int[] lookupValues) {
		this.scaleHorizontal = scale;
		this.lookupValues = lookupValues;
	}
	
	public /*@ pure @*/ int getValue(SensorValue sv) {
		ScaleIndex si = scaleHorizontal.lookupValue(sv);
		int i = si.getIntPart();
		int f = si.getFracPart();
		int v = lookupValues[i];
		if(i<lookupValues.length-1) {
			int vn = lookupValues[i+1];
			v = v + (vn - v)*f/100; // linear interpolate
		}
		return v;
	}
}
