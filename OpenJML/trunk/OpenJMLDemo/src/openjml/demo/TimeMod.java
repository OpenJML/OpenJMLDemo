package sv_rac_solutions;

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
	
	private /*@ spec_public @*/ byte hour;
	private /*@ spec_public @*/ byte minute;

	/*@
	 	requires h >= getHour();
	 	requires m >= getMinute();
	 	requires 0 <= m && m < 60;
	 	requires 0 <= h && h < 24;
		ensures time == h * 60 + m;
		ensures hour == h && minute == m; 
	 */
	public void setTime(byte h, byte m) {
		hour = h;
		minute = m;
	} 

	/*@
	  	requires h != null;
	  	requires h.getHour() >= getHour();
	  	requires h.getMinute() >= getMinute();
	  	ensures this.time == h.time;
	 */
	public void setTime(Time h) {
		setTime(h.getHour(), h.getMinute());
		//@ assert h.getHour() == getHour();
		//@ assert h.getMinute() == getMinute();
		//@ assert h.time == time;
		//@ assert time == this.time;
	} 

	/*@ 
	 	//ensures \result == (time - minute) / 60;
	 	ensures \result == hour;
	 */
	public /*@ pure helper */ byte getHour(){
		return hour;
	}

	/*@ 
	 	//ensures \result == time - (hour * 60);
	 	ensures \result == minute;
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
	 	ensures bArray[offset] == (time - minute) / 60;
	 	ensures bArray[offset+1] == time - (hour * 60);
	 */
	public short  getTime(byte [] bArray, short offset){
		short aux = offset;
		bArray[aux++] = hour;
		bArray[aux++] = minute;	
		return (short) (offset + (short) 2);
	}
	
	//@ ensures getHour() == 0 && getMinute() == 0;
	public Time() {}
	
	public static void main(String[] args) {
		Time t = new Time();
		t.setTime((byte)10, (byte)01);  // Fails if Time() is not specified 
		t.getHour();
		t.getMinute();
	}
}
