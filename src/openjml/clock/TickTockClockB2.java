// In this instance of the example, we introdu8ce a bug.
// In the then branch of (if (second == 60) of method tick,
// the value of 'second' is not set to 0.  We then attempt to 
// record the value of 'second' using a lbl expression. However,
// the call of getSecond() in that expression issues a UndefinedCalledMethodPrecondition
// warning. This is because the preconditions for calling getSecond() include the
// object invariants, which require that 'second <= 59'. Since at this point 
// 'second' is 60, the precondition is violated and it is not legal to call
// 'getSecond()'.
//
// The way out of this problem is to declare getSecond() as a helper method
//
// But that still leaves a problem in that the postconditions of getSecond() 
// require getSecond() to return a value <= 59.

package openjml.clock;
public class TickTockClockB2 {
    //@ public nullable model JMLDataGroup _time_state;

	//@ public invariant 0 <= hour && hour <= 23;
	public int hour; //@ in _time_state;

	//@ public invariant 0 <= minute && minute <= 59;
	public int minute; //@ in _time_state;

	//@ public invariant 0 <= second && second <= 59;
	public int second; //@ in _time_state;

	//@
	//@ ensures getHour() == 12 && getMinute() == 0 && getSecond() == 0;
	public /*@ pure @*/ TickTockClockB2() {
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
		if (second == 60) { minute++; /*@ ghost int s = (\lbl SECOND getSecond()); */   }
		if (minute == 60) { minute = 0; hour++; }
		if (hour == 24) { hour = 0; }
	}
}
