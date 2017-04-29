public class Timer {
  
  public int minute;
  public int hour;
  
  //@ ensures hour == hours && minute == minutes;
  /*@ pure */ public Timer(int hours, int minutes) {
    hour = hours;
    minute = minutes;
  }
  
  //@ ensures \result == minute;
  /*@ pure */ public int minute() {
    return minute;
  }
  
  //@ ensures \result == hour;
  public int hour() {
    return hour;
  }
  
  // Decrement timer by one minute
  /*@   requires minute > 0;
    @   assignable minute;
    @   ensures minute == \old(minute) - 1;
    @ also
    @   requires minute == 0;
    @   assignable minute, hour;
    @   ensures minute == 59 && hour == \old(hour) - 1;
    @*/
  // Decrement timer by one minute
  public void tick() {
    minute--;
    if (minute < 0) { minute = 59; hour--; }
  }
  
  // returns true when timer is at 0
  //@ ensures \result == (minute == 0 && hour == 0);
  /*@ pure */ public boolean done() {
	    return (minute == 0 && hour == 0);
  }
}
