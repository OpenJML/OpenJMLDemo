
public class SensorValue {

	int value;
	final int failSafe;
	final int minValue;
	final int maxValue;

	//@ invariant minValue <= value;
	//@ invariant value <= maxValue;

	//@ invariant minValue <= maxValue;

	//@ invariant minValue <= failSafe;
	//@ invariant failSafe <= maxValue;
	
	
	/*@ normal_behavior
	  @ requires minValue <= failSafe;
	  @ requires failSafe <= maxValue;
	  @ requires minValue <= maxValue;
	  @ ensures this.minValue == minValue;
	  @ ensures this.maxValue == maxValue;
	  @ ensures this.failSafe == failSafe;
	  @ pure 
	  @*/
	public SensorValue(int failSafe, int minValue, int maxValue) {
		this.failSafe = failSafe;
		this.minValue = minValue;
		this.maxValue = maxValue;
		this.value = failSafe;
	}
	
	/*@ normal_behavior
	  @ ensures this.value == newValue || this.value == this.failSafe;
	  @ assignable this.value; @*/
	public void readSensor(int newValue) {
		if(newValue < minValue || newValue > maxValue) {
			this.value = failSafe;
		}else{
			this.value = newValue;
		}
	}
	
	/*@ normal_behavior
	  @ ensures \result == this.value; @*/
	public /*@ pure @*/ int getValue() {
		return this.value;
	}
	
}
