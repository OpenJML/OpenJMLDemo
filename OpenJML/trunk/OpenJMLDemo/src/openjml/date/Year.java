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
 *  Original author: Thierry Bressure
 *------------------------------------------------------------------------------
 */


/**
 * Classe qui mod�lise une ann�e. Les ann�es sont compt�es � partir de 1900.
 * Cette classe n'est utilis�e que pour valider la correction d'une ann�e.
 * Une ann�e est correcte si son ordinal est compris entre
 * <code>Annee.MIN</code> et <code>Annee.MAX</code>.
 */
public abstract class Year extends Object{
 
	////////////////      ATTRIBUTS       ////////////////

	/**	le logiciel �tant impl�menter en 1999, cette ann�e sera l'ann�e
	 *	minimum
	 */
 	public static final byte MIN = (byte)99;

	/**	Ann�e maximum qui nous est impos�e par la magnitude de l'octet
	 *	en Java
	 */
	public static final byte MAX = (byte)127;

	//@ public static invariant MIN == 99;
	//@ public static invariant MAX == 127;


	///////////////     CONSTRUCTEUR     ////////////////



	////////////////       METHODES      ///////////////


	//@ ensures \result <==> (y >= Year.MIN && y <= Year.MAX);
	public /*@ pure @*/ static boolean check(byte y) {
		return ((y >= Year.MIN) && (y <= Year.MAX));
	}

    //@ requires y >= Year.MIN;
	//@ requires y <= Year.MAX;
	//@ ensures \result >= Year.MIN && \result <= Year.MAX;
	public /*@ pure @*/ static byte nextYear(byte y) {
		byte r = (byte)(y + 1);
		if(r > MAX) r = MIN;
		return r;
	}
}
