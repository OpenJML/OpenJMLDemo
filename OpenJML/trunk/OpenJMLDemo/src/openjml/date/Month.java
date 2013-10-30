package sv_esc_solutions;

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
 *  Original author: Thierry Bressure
 *------------------------------------------------------------------------------
 */



public abstract class Month extends Object{


	////////////////      ATTRIBUTS       ////////////////

	public static final byte JANUARY	= (byte)1;
	public static final byte FEBRUARY	= (byte)2;
	public static final byte MARCH		= (byte)3;
	public static final byte APRIL		= (byte)4;
	public static final byte MAY		= (byte)5;
	public static final byte JUNE		= (byte)6;
	public static final byte JULY		= (byte)7;
	public static final byte AUGUST		= (byte)8;
	public static final byte SEPTEMBER	= (byte)9;
	public static final byte OCTOBER	= (byte)10;
	public static final byte NOVEMBER	= (byte)11;
	public static final byte DECEMBER	= (byte)12;

	public static final byte MIN	= Month.JANUARY;
	public static final byte MAX	= Month.DECEMBER;

	//@ public static invariant JANUARY	== 1;
	//@ public static invariant FEBRUARY == 2;
	//@ public static invariant MARCH == 3;
	//@ public static invariant APRIL == 4;
	//@ public static invariant MAY	== 5;
	//@ public static invariant JUNE == 6;
	//@ public static invariant JULY == 7;
	//@ public static invariant AUGUST == 8;
	//@ public static invariant SEPTEMBER == 9;
	//@ public static invariant OCTOBER == 10;
	//@ public static invariant NOVEMBER == 11;
	//@ public static invariant DECEMBER == 12;

	//@ public static invariant MIN == JANUARY;
	//@ public static invariant MAX == DECEMBER;


	///////////////     CONSTRUCTEUR     ////////////////



	////////////////       METHODES      ///////////////

	//@ ensures \result <==> (m >= Month.MIN && m <= Month.MAX);
	public /*@ pure @*/ static boolean check(byte m) {
		return ((m >= Month.MIN) && (m <= Month.MAX));
	}
	
    //@ requires m >= MIN && m <= MAX;
	//@ ensures \result >= MIN && \result <= MAX;
	public /*@ pure @*/ static byte nextMonth(byte m) {
		byte r = (byte)(m + 1);
		if(r > MAX) r = MIN;
		return r;
	}


}
