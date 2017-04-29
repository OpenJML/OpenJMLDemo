public class Timer {
  
  public int minute;
  public int hour;
  
  // create a Timer with the given time remaining
  public Timer(int hours, int minutes) {
    hour = hours;
    minute = minutes;
  }
  
  public int minute() {
    return minute;
  }
  
  public int hour() {
    return hour;
  }
  
  // Decrement timer by one minute
  public void tick() {
    minute--;
    if (minute < 0) { minute = 59; hour--; }
  }
  
  // returns true when timer is at 0
  public boolean done() {
	    return (minute == 0 && hour == 0);
  }
}
