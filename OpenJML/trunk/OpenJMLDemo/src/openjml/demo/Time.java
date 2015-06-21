//package sv_rac_solutions;

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

/* model the time for the transactions*/
public class Time extends Object{

	//@ ensures time == 0;
	public Time() {
		hour = 0;
		minute = 0;
	}

	//@ public model int time;
	//@ represents time <- hour * 60 + minute;
	
	//@ public model int maxTime;
	//@ represents maxTime <- 23 * 60 + 59;

	/*@
	 	public invariant time >= 0;
	 	public invariant time <= maxTime;
	 	
	 	public invariant 0 <= minute && minute < 60;
	 	public invariant 0 <= hour && hour < 24;
	 	
	 	public constraint time >= \old(time);
	 */
	
	private /*@ spec_public @*/ byte hour; //@ in time;
	private /*@ spec_public @*/ byte minute; //@ in time;

	/*@
	 	requires h >= getHour();
	 	requires m >= getMinute();
	 	requires 0 <= m && m < 60;
	 	requires 0 <= h && h < 24;
	 	assignable time;
		ensures time == h * 60 + m;
	 */
	public void setTime(byte h, byte m) {
		hour = h;
		minute = m;
	} 

	/*@
	  	requires h != null;
	  	requires h.getHour() >= getHour();
	  	requires h.getMinute() >= getMinute();
	  	assignable time;
	  	ensures this.time == h.time;
	 */
	public void setTime(Time h) {
		setTime(h.getHour(), h.getMinute());
	} 

	/*@ 
	 	ensures \result == hour; //ensures \result == (time - minute) / 60;
	 */
	public /*@ pure helper */ byte getHour(){
		return hour;
	}

	/*@ 
	 	ensures \result == minute; //\result == time - (hour * 60);
	 */
	public /*@ pure helper */ byte getMinute(){
		return minute;
	}

	/*@
	 	requires bArray != null;
	 	
	 	requires offset >= 0;
	 	requires offset < 32766; //prevents overflowing of offset/aux
	 	
	 	requires 0 <= offset && offset < bArray.length - 1;
	 	requires bArray.length >= 2;
	 	
	 	ensures (\forall int i; 0 <= i && i < offset; bArray[i] == \old(bArray[i]));
	 	ensures bArray[offset] == hour; // (time - minute) / 60;
	 	ensures bArray[offset+1] == time - (hour * 60);
	 */
	public short  getTime(byte [] bArray, short offset){ // FIXME - this test works if all the shorts are ints - so the problem is with numeric conversion
		short aux = offset;
		bArray[aux++] = hour;
		bArray[aux++] = minute;	
		return (short) (offset + (short) 2);
	}
	
	public static void main(String[] args) {
		Time t = new Time();
		t.setTime((byte)10, (byte)01);
		t.getHour();
		t.getMinute();
	}
}
