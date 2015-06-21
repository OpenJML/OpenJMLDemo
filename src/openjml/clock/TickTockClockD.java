package openjml.clock;
public class TickTockClockD {
    //@ public model JMLDataGroup _time_state;

	//@ protected invariant 0 <= hour && hour <= 23;
	protected int hour; //@ in _time_state;

	//@ protected invariant 0 <= minute && minute <= 59;
	protected int minute; //@ in _time_state;

	//@ protected invariant 0 <= second && second <= 59;
	protected int second; //@ in _time_state;

	//@ public model int getTime; //@ in _time_state;  // FIXME - this in clause does not seem to matter
	//@ protected represents getTime = hour*3600 + minute*60 + second;

	//@ assignable _time_state;
	//@ ensures getTime == 12*60*60;
	public /*@ pure @*/ TickTockClockD() {
		hour = 12; minute = 0; second = 0;
	}

	/*@  requires getTime < 24*60*60-1;
	  @  ensures getTime == \old(getTime) + 1;
	  @ also
	  @  requires getTime == 24*60*60-1;
	  @  ensures getTime == 0;
      @*/
	public void tick() { 
		second++;
		if (second == 60) { second = 0; minute++; }
		if (minute == 60) { minute = 0; hour++; }
		if (hour == 24) { hour = 0; }
		//@ reachable;
	}
}
/* Version of example using one model field. Everything validates
 */
