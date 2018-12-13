// Using fields instead of getHour()... functions; need to adjust visibility
// Need to embellish postconditions of getHour()...
// Issue with evaluating a method inside an \old 

package openjml.clock;
public class TickTockClockA1 {
    //@ public model JMLDataGroup _time_state;

	//@ protected invariant 0 <= hour && hour <= 23;
	//@ spec_public
	protected int hour; //@ in _time_state;

	//@ protected invariant 0 <= minute && minute <= 59;
	//@ spec_public
	protected int minute; //@ in _time_state;

	//@ protected invariant 0 <= second && second <= 59;
	//@ spec_public
	protected int second; //@ in _time_state;

	//@ ensures getHour() == 12 && getMinute() == 0 && getSecond() == 0;
	public /*@ pure @*/ TickTockClockA1() {
		hour = 12; minute = 0; second = 0;
	}

	//@ public normal_behavior
	//@ requires true;
	//@ ensures 0 <= \result && \result <= 23;
	//@ ensures \result == hour;
	public /*@ pure @*/ int getHour() { return hour; }

	//@ public normal_behavior
	//@ ensures 0 <= \result && \result <= 59;
	//@ ensures \result == minute;
	public /*@ pure @*/ int getMinute() { return minute; }

	//@ public normal_behavior
	//@ ensures 0 <= \result;
	//@ ensures \result <= 59;
	//@ ensures \result == second;
	public /*@ pure @*/ int getSecond() { return second; }

	/*@  requires getSecond() < 59;
      @  // assignable hour, minute, second; // NB for expository purposes only
      @  assignable _time_state;
      @  ensures getSecond() == \old(getSecond() + 1) &&
      @          getMinute() == \old(getMinute()) &&
      @          getHour() == \old(getHour());
      @ also
      @  requires getSecond() == 59;
      @  assignable _time_state;
      @  ensures getSecond() == 0;
      @  ensures (* hours and minutes are updated appropriately *);
      @*/
	public void tick() {
		second++;
		if (second == 60) { second = 0; minute++; /*  @ ghost int s = (\lbl SECOND getSecond()); */ }
		if (minute == 60) { minute = 0; hour++; }
		if (hour == 24) { hour = 0; }
	}
}
/* Following on TickTockClockA, the hour, minute, second fields are declared spec_public so they may
 * be used in the get...() postconditions. But now they are public and may not be used in protected
 * invariants.
 */