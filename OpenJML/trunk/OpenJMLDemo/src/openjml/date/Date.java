package date;

/**
 * Copyright (c) 1999 GEMPLUS group. All Rights Reserved.
 *------------------------------------------------------------------------------
 *  Project name:  PACAP  - cas d'�tude -
 *
 *
 *  Platform    :  Java virtual machine
 *  Language    :  JAVA 1.1.x
 *  Devl tool   :  Symantec VisualCafe
 *
 *  @author: Thierry Bressure
 *  @version 1
 *------------------------------------------------------------------------------
 */

// added by Rodolphe Muller on 06/07/2000

/* model the date to the date-month-year format using the constants of the abstract
 classes Day, Month, Year of this package*/
public class Date extends Object {

    /*@
        public invariant day >= Day.MIN && day <= Day.MAX ;
        public invariant month >= Month.MIN && month <= Month.MAX ;
        public invariant year >= Year.MIN && year <= Year.MAX ;
      @*/
 
	////////////////      ATTRIBUTES       ////////////////

	 /*@ spec_public */ private byte day		= Day.MIN;
	 /*@ spec_public */ private byte month		= Month.MIN;    
	 /*@ spec_public */ private byte year		= Year.MIN;

 
	///////////////     CONSTRUCTOR     ////////////////

	/* the default constructor initialize the date to january, 1rst 1999*/

	/*@ ensures day == Day.MIN && month == Month.MIN && year == Year.MIN;
	    assignable day, month, year; */	
	public Date() {
		super();
	}

    /**
	 *	@param d the day of the month
	 *	@param m the month of the year
	 *	@param y the year counted from 1900
	 *	@exception DateException  is thrown if the arguments provide a date not coherent or before
	    January, 1rst 1999*/

	/*@ 
          requires d >= Day.MIN && d <= Day.MAX &&
                   m >= Month.MIN && m <= Month.MAX &&
                   y >= Year.MIN && y <= Year.MAX;
          ensures day == d && month == m && year == y; 
          // assignable day, month, year;
     */	 
	public Date(byte d, byte m, byte y) {
		super();
		day = d;
		month = m;
		year = y;
	}

	/*@ requires d != null;
	    ensures this.equals(d);
	    // assignable \everything;
	 */
	public Date(Date d) {
		this(d.day, d.month, d.year);
	}

	////////////////       METHODS      ///////////////

    /*@ 
        modifies day, month, year;
        requires d >= Day.MIN && d <= Day.MAX &&
                 m >= Month.MIN && m <= Month.MAX &&
                 y >= Year.MIN && y <= Year.MAX;
        ensures day == d && year == y && month == m ;
     */
	public void setDate(byte d, byte m, byte y) {
		day = d;
		month = m;
		year = y;
	}

	/*@ 
        modifies day, month, year ;
        requires d != null;
        ensures day == d.day;
        ensures year == d.year;
        ensures month == d.month ;
     */
	public void setDate(Date d) {
		setDate(d.getDay(), d.getMonth(), d.getYear());
	}

	/* check if the date is before (strictly) to the one provided
	 *	@param d : date used to compare the date of this class*/

    /*@ 
        requires d != null ;
        ensures \result == ((d.year > year) ||
                            (d.year == year && d.month > month) ||
		                    (d.year == year && d.month == month && d.day > day)
		                   ) ;
      */
	/*@ pure */ public boolean before(Date d) {
		if(d.getYear() < year) return false;
		else if(d.getYear() > year) return true;
		else if(d.getMonth() < month) return false;
		else if(d.getMonth() > month) return true;
		else if(d.getDay() <= day) return false;
		else return true;
	}

    /*@ ensures \result == day; */
	/*@pure */ public  byte getDay() {
		return day;
	}

	/*@ ensures \result == month; */
	/*@pure */ public byte getMonth() {
		return month;
	}

    /*@ ensures \result == year; */
	/*@pure */ public byte getYear() {
		return year;
	}

    /*@ ensures difference_in_days(\result) == 1 && before(\result);
        ensures \result != null;
        assignable \nothing;
    */
	public Date tomorrow () {
		Date tomorrow = new Date(this);
		if (day == Day.MAX) {
			if (month == Month.MAX) {
				//@ assert year >= Year.MIN && year <= Year.MAX;
				tomorrow.year = Year.nextYear(year);
			}
			tomorrow.month = Month.nextMonth(month);
		}
		tomorrow.day = Day.nextDay(day);
		return tomorrow;
	}
	
	/*@ ensures \old(this).difference_in_days(this) == 1 && \old(this).before(this);
	*/	
	public void setToTomorrow () {
		setDate(tomorrow());
	}
			
	/*@ requires days != null && \nonnullelements(days);
	    ensures \result == (\forall int i;
	      0 <= i && i < days.length - 1;
	      days[i].difference_in_days(days[i + 1]) == 1 && days[i].before(days[i + 1]));
	 */
	public /*@ pure @*/ boolean consecutive(Date[] days) {
		boolean res = true;
		//@ loop_invariant i>=0 && i<= days.length;
		for (int i = 0; i < days.length - 1 && res; i++){
			res = (days[i].tomorrow()).equals(days[i + 1]);
		};
		return res;
	}

	// This is not a very meaningfull specification
	// Using model variables with an abstract representation of dates (e.g., the distance to the year 0) a nicer specification can be given
	/*@ requires d != null;
        ensures \result == (d.year - year)*372 - (day + (month - 1) * 31) + (d.day + (d.month -1) * 31); 
	 */
	/*@ pure */ public int difference_in_days(Date d){
		int dist1Jan1 = day + (month - 1)* 31;
		int dist1Jan2 = d.day + (d.month - 1) * 31;
		return (d.year - year)*372 - dist1Jan1 + dist1Jan2; 
	}
	
	/*@ requires date != null;
	    ensures \result == (date.day == this.day && date.month == this.month && date.year == this.year);
	 */
	/*@ pure */ public boolean equals(Date date) {
		return (date.day == day) && (date.month == month) && (date.year == year);
	}
	
    /*@ 
        modifies day, month, year ;
        ensures day == d && year == y && month == m ;
        signals (Exception) d < Day.MIN || d > Day.MAX || m < Month.MIN || m > Month.MAX || y < Year.MIN || y > Year.MAX;
     */	
	public void setDate(byte d, byte m, byte y, byte bla) throws Exception {
		if (Day.check(d) && Month.check(m) && Year.check(y)) {
			day = d;
			month = m;
			year = y;
		}
		else throw new Exception();
	}
	
}
