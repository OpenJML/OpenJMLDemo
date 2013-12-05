/*
 * Fall 2013 CSCI181G - Homework 6
 * Static and Runtime Checking
 */



/**
 * A settable clock that tells 24-hour time. This class is _not_ immutable.
 * 
 * This class needs to be statically verified and may or may not have 
 * errors in its implementation.
 * 
 * @author Daniel M. Zimmerman
 * @author YOUR NAME HERE
 * @version 2013-11-04
 */
public class SettableClock extends Clock {
  // Constructor
  
  /**
   * Constructs a new SettableClock with the time set to 00:00:00.
   */
  //@ ensures hours == 0 && minutes == 0 && seconds == 0;
  //@ assignable \everything;  // this is a hack to allow assignable to check, why necessary??
  public SettableClock() {
    super(0, 0, 0);
  }

  // Commands
  
  /*
   * Note, on the following command, that an IllegalArgumentException
   * is thrown if a bad time is specified; you should _not_ restrict
   * the input but should instead write a specification that includes
   * the IllegalArgumentException.
   */
  
  /*@ public normal_behavior
        requires legalTime(the_hours, the_minutes, the_seconds);
        ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
      also public exceptional_behavior
        requires !legalTime(the_hours, the_minutes, the_seconds);
        assignable \nothing;
        signals (IllegalArgumentException) true;
        signals_only IllegalArgumentException;
   */
  /**
   * Sets the time on the clock to the specified time. 
   *
   * @param the_hours The hours to set.
   * @param the_minutes The minutes to set.
   * @param the_seconds The seconds to set.
   * @exception IllegalArgumentException if an invalid time is specified.
   */
  public void set(final int the_hours, final int the_minutes, final int the_seconds)
    throws IllegalArgumentException {
    if (the_hours < 0 || HOURS_IN_DAY <= the_hours || 
        the_minutes < 0 || MINS_IN_HOUR <= the_minutes ||
        the_seconds < 0 || SECS_IN_MIN <= the_seconds) {
      throw new IllegalArgumentException("Invalid time specified.");
    }
    setHours(the_hours);
    setMinutes(the_minutes);
    setSeconds(the_seconds);
  }
}
