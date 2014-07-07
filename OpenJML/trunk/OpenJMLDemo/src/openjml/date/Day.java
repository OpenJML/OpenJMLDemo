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



public abstract class Day extends Object{
    

	////////////////      ATTRIBUTS       ////////////////

	public static final byte MIN	= (byte)1;
	public static final byte MAX	= (byte)31;
	
	//@ public static invariant MIN == 1;
	//@ public static invariant MAX == 31;

	///////////////     CONSTRUCTEUR     ////////////////
    


	////////////////       METHODES      ///////////////
 
	//@ ensures \result <==> (d >= Day.MIN && d <= Day.MAX);
	public /*@ pure @*/ static boolean check(byte d){
		if((d >= Day.MIN) && (d <= Day.MAX)) {
			return true;
		} else {
			return false;
		}
	}
	
    //@ requires d >= MIN && d <= MAX;
	//@ ensures \result >= MIN && \result <= MAX;
	public /*@ pure @*/ static byte nextDay(byte d) {
		byte r = (byte)(d + 1);
		if(r > MAX) r = MIN;
		return r;
	}

}
