/*
 * Fall 2013 CSCI181G - Final Exam
 * Static and Runtime Checking
 * SOLUTION - DO NOT DISTRIBUTE
 */

package dmz;

/**
 * A date class that performs calulations for the standard Gregorian
 * calendar. It is partially specified; the specifications already in
 * the class must be maintained and additional specifications must be
 * added to make the class successfully ESC. 
 * 
 * @author Daniel M. Zimmerman
 * @version 2013-12-11
 */
public class Date {
  // Useful Constants
  
  /**
   * The number of seconds in a minute.
   */
  public static final int SECS_IN_MIN = 60;
  
  /**
   * The number of minutes in an hour.
   */
  public static final int MINS_IN_HOUR = 60;
  
  /**
   * The number of hours in a day.
   */
  public static final int HOURS_IN_DAY = 24;
  
  
  // Instance Fields
  
  /**
   * The current hours on the clock.
   */
  private int my_hours;
  //@ in hours;
  //@ public model int hours;
  //@ private represents hours = my_hours;
  
  /**
   * The current minutes on the clock.
   */
  private int my_minutes;
  //@ in minutes;
  //@ public model int minutes;
  //@ private represents minutes = my_minutes;
  
  /**
   * The current seconds on the clock.
   */
  private int my_seconds;
  //@ in seconds;
  //@ public model int seconds;
  //@ private represents seconds = my_seconds;

  // invariant: the time is always reasonable
  //@ public invariant legalTime(hours, minutes, seconds);
  
  // Constructor
  
  /* 
   * the constructor should have appropriate constructs that force
   * the client to validate the data passed in.
   */
  
  /**
   * Constructs a new Clock set to the specified time.
   * 
   * @param the_hours The initial setting for hours.
   * @param the_minutes The initial setting for minutes.
   * @param the_seconds The initial setting for seconds.
   */
  //@ requires legalTime(the_hours, the_minutes, the_seconds);
  //@ ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
  //@ assignable hours, minutes, seconds;
  public Clock(final int the_hours, final int the_minutes, final int the_seconds) {
    my_hours = the_hours;
    my_minutes = the_minutes;
    my_seconds = the_seconds;
  }
  
  // Queries
  
  // model features for legal time and total number of seconds on the clock
  // note no bodies, since we're only doing ESC
  
  /*@ ensures \result <==> 0 <= the_hours && the_hours < HOURS_IN_DAY &&
                           0 <= the_minutes && the_minutes < MINS_IN_HOUR && 
                           0 <= the_seconds && the_seconds < SECS_IN_MIN;
      public pure helper model boolean legalTime
      (int the_hours, int the_minutes, int the_seconds);
   */
  
  //@ public model int total_seconds;
  /*@ public represents total_seconds = 
        hours * MINS_IN_HOUR * SECS_IN_MIN + minutes * SECS_IN_MIN + seconds;
   */
  
  /**
   * @return The current hours on the clock.
   */
  //@ ensures \result == hours;
  public /*@ pure */ int hours() {
    return my_hours;
  }
  
  /**
   * @return The current minutes on the clock.
   */
  //@ ensures \result == minutes;
  public /*@ pure */ int minutes() {
    return my_minutes;
  }
  
  /**
   * @return The current seconds on the clock.
   */
  //@ ensures \result == seconds;
  public /*@ pure */ int seconds() {
    return my_seconds;
  }
  
  /**
   * Checks to see if the time on this clock is later than the time
   * on the specified Clock.
   * 
   * @param the_other_clock The other Clock to check.
   * @return true if this Clock has a later time, false otherwise.
   */
  //@ ensures \result <==> 0 < difference(the_other_clock);
  public /*@ pure */ boolean later(final Clock the_other_clock) {
    return 0 < difference(the_other_clock);
  }
  
  /**
   * Checks to see if the time on this clock is earlier than the time
   * on the specified Clock.
   * 
   * @param the_other_clock The other Clock to check.
   * @return true if this Clock has an earlier time, false otherwise.
   */
  //@ ensures \result <==> difference(the_other_clock) < 0;
  public /*@ pure */ boolean earlier(final Clock the_other_clock) {
    return difference(the_other_clock) < 0;
  }

  /**
   * Computes the difference in seconds between the time on this Clock and
   * the time on the specified Clock. If the specified Clock has a later
   * time, the difference is negative; if the specified Clock has an earlier
   * value, the difference is positive; if the two clocks have the same value,
   * the difference is 0.
   * 
   * @param the_other_clock The other Clock to use.
   * @return The difference between the time on this Clock and the time
   *  on the other Clock, in seconds.
   */
  //@ ensures \result == total_seconds - the_other_clock.total_seconds;
  public /*@ pure */ int difference(final Clock the_other_clock) {
    final int seconds = 
      hours() * MINS_IN_HOUR * SECS_IN_MIN + minutes() * SECS_IN_MIN + seconds();
    final int other_seconds = 
      the_other_clock.hours() * MINS_IN_HOUR * SECS_IN_MIN +
      the_other_clock.minutes() * SECS_IN_MIN + the_other_clock.seconds();
    
    return seconds - other_seconds;
  }
  
  // Commands
  
  /**
   * Sets the hours on the clock.
   * 
   * @param the_hours The new value for hours.
   */
  //@ requires legalTime(the_hours, minutes, seconds);
  //@ ensures hours == the_hours;
  //@ assignable hours;
  //@ signals_only \nothing;
  protected void setHours(final int the_hours) {
    my_hours = the_hours;
  }

  /**
   * Sets the minutes on the clock.
   * 
   * @param the_minutes The new value for minutes.
   */
  //@ requires legalTime(hours, the_minutes, seconds);
  //@ ensures minutes == the_minutes;
  //@ assignable minutes;
  //@ signals_only \nothing;
  protected void setMinutes(final int the_minutes) {
    my_minutes = the_minutes;
  }
  
  /**
   * Sets the seconds on the clock.
   * 
   * @param the_seconds The new value for seconds.
   */
  //@ requires legalTime(hours, minutes, the_seconds);
  //@ ensures seconds == the_seconds;
  //@ assignable seconds;
  //@ signals_only \nothing;
  protected void setSeconds(final int the_seconds) {
    my_seconds = the_seconds;
  }
  
  //@ requires total_seconds < HOURS_IN_DAY * MINS_IN_HOUR * SECS_IN_MIN - 1;
  //@ ensures total_seconds == \old(total_seconds) + 1;
  //@ also 
  //@ requires total_seconds == HOURS_IN_DAY * MINS_IN_HOUR * SECS_IN_MIN - 1;
  //@ ensures total_seconds == 0;
  /**
   * Ticks the clock forward by one second. If we have reached the
   * end of the day (that is, we tick forward from 23:59:59), the clock 
   * should wrap around to 00:00:00.
   */
  public void tick() {
    my_seconds += 1;
    
    if (my_seconds >= SECS_IN_MIN) {
      my_minutes += 1;
      my_seconds = 0;
    }
    
    if (my_minutes >= MINS_IN_HOUR) {
      my_hours += 1;
      my_minutes = 0;
    }
    
    if (my_hours >= HOURS_IN_DAY) {
      my_hours = 0;
    }
  }
}
