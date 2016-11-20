package openjml.clock;
public class TickTockClock1 {
    //@ public nullable model JMLDataGroup _time_state;

	//@ protected invariant 0 <= hour && hour <= 23;
	protected int hour; //@ in _time_state;

	//@ protected invariant 0 <= minute && minute <= 59;
	protected int minute; //@ in _time_state;

	//@ protected invariant 0 <= second && second <= 59;
	protected int second; //@ in _time_state;

	//@ assignable _time_state; ensures getHour() == 12 && getMinute() == 0 && getSecond() == 0;
	public /*@ pure @*/ TickTockClock1() {
		hour = 12; minute = 0; second = 0;
	}

	//@ requires true;
	//@ ensures 0 <= \result && \result <= 23;
	public /*@ pure @*/ int getHour() { return hour; }

	//@ ensures 0 <= \result && \result <= 59;
	public /*@ pure @*/ int getMinute() { return minute; }

	//@ ensures 0 <= \result;
	//@ ensures \result <= 59;
	public /*@ pure @*/ int getSecond() { return second; }

	/*@  requires getSecond() < 59;
      @  //assignable hour, minute, second; // NB for expository purposes only
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
		if (second == 60) { second = 0; minute++; }
		if (minute == 60) { minute = 0; hour++; }
		if (hour == 24) { hour = 0; }
	}
}
/* This example implements a clock, represented by values of hours, minutes, seconds;
 * the time is incremented by tick().
 * This version has this problem:
 *   The postcondtions of rgetHour(), getMinute(), getSecond() only constrain the
 *   values of their results, but do not relate the results to the values of hour, minute, second.
 *   Consequently the postconditions of neither the constructor nor tick() can be proved.
 */