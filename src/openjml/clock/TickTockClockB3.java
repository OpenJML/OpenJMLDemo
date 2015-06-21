// 
// 
//  

package openjml.clock;
public class TickTockClockB3 {
    //@ public model JMLDataGroup _time_state;

	//@ public invariant 0 <= hour && hour <= 23;
	public int hour; //@ in _time_state;

	//@ public invariant 0 <= minute && minute <= 59;
	public int minute; //@ in _time_state;

	//@ public invariant 0 <= second && second <= 59;
	public int second; //@ in _time_state;

	//@ assignable _time_state; 
	//@ ensures getHour() == 12 && getMinute() == 0 && getSecond() == 0;
	public /*@ pure @*/ TickTockClockB3() {
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
	//@ helper
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
		if (second == 60) { minute++; /*@ ghost int s = (\lbl SECOND getSecond()); */ } // ERROR here
		if (minute == 60) { minute = 0; hour++; }
		if (hour == 24) { hour = 0; }
	}
	// Note - no error reported in tick because of the ensures clauses on getSecond()
	// tick() validates, but it is not actually correct - the fact that getScond() does not validate should be an alert
}
