public class Timer {
  
  public int minute;
  public int hour;
  
  //@ ensures hour == hours && minute == minutes;
  public Timer(int hours, int minutes) {
    hour = hours;
    minute = minutes;
  }
  
  //@ ensures \result == minute;
  public int minute() {
    return minute;
  }
  
  //@ ensures \result == hour;
  public int hour() {
    return hour;
  }
  
  // Decrement timer by one minute; returns true when timer is at 0
  /*@   requires minute > 0;
    @   assignable minute;
    @   ensures minute == \old(minute) - 1;
    @ also
    @   requires minute == 0;
    @   assignable minute, hour;
    @   ensures minute == 59 && hour == \old(hour) - 1;
    @*/
  public boolean tick() {
    minute--;
    if (minute < 0) { minute = 59; hour--; }
    return (minute == 0 && hour == 0);
  }
}
