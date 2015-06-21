package openjml.clock;
public class TickTockClockC {
    //@ public model JMLDataGroup _time_state;

	//@ protected invariant 0 <= hour && hour <= 23;
	protected int hour; //@ in _time_state;

	//@ protected invariant 0 <= minute && minute <= 59;
	protected int minute; //@ in _time_state;

	//@ protected invariant 0 <= second && second <= 59;
	protected int second; //@ in _time_state;

	//@ public model int getHour;
	//@ protected represents getHour = hour;

	//@ public model int getMinute;
	//@ protected represents getMinute = minute;

	//@ public model int getSecond;
	//@ protected represents getSecond = second;

	//@ assignable _time_state;
	//@ ensures getHour == 12 && getMinute == 0 && getSecond == 0;
	public /*@ pure @*/ TickTockClockC() {
		hour = 12; minute = 0; second = 0;
	}

	/*@  requires getSecond < 59;
      @  assignable _time_state;
      @  ensures getSecond == \old(getSecond + 1) &&
      @          getMinute == \old(getMinute) &&
      @          getHour == \old(getHour);
      @ also
      @  requires getSecond == 59;
      @  assignable _time_state;
      @  ensures getSecond == 0;
      @  ensures (* hours and minutes are updated appropriately *);
      @*/
	public void tick() { 
		second++;
		if (second == 60) { second = 0; minute++; /*@ ghost int s = (\lbl SEC getSecond); */ }
		if (minute == 60) { minute = 0; hour++; }
		if (hour == 24) { hour = 0; }
	}
}
/* Version of example using model fields with representations.
 */
