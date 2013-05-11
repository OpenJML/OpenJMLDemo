package openjml.test;

import java.util.AbstractSet;
import java.util.Iterator;

//import org.jmlspecs.annotation.Pure;


///*@ model */ import java.io.*;

////@ model import java.lang.*;
////@ model import java.lang.* 
////@ model import 
////@ model import java.lang.*;

//public class Test1 /*@ { weakly */ { // crashes
public class Test1 extends AbstractSet<Integer> {
	public Object m() {
		return new AbstractSet<Integer>() {
			public boolean equals(Object o ) { return true;}
			public int hashcode() { return 0; }
			public void removeAll() {}
			public Iterator<Integer> iterator() { return null; }
			public int size() { return 0; }
		};
	}
	public boolean equals(Object o ) { return true;}
	public int hashcode() { return 0; }
	public void removeAll() {}
	public Iterator<Integer> iterator() { return null; }
	public int size() { return 0; }

//	
////	@ constraint true for bn(), Test1.*, this.*, bn(int), bn(Object), bn.*();
////	@ constraint true for bn.this.*,  bn.super.*;
//	
////	//@ requires i > 0;
////	//@ ensures \result != 0;
////	public int m(int i) {
////		
////		return 0;
////	}
////	
////	public int p;
////
////	//@ requires i > 0;
////	//@ ensures \result == 0 ;
////	@Pure
////	public int n(int i) {
////		p++;
////		return 0;
////	}
//	
////	//@ non_null
////	public Boolean b() {
////		return Boolean.valueOf(true); //Boolean.TRUE;
////	}
//	/*@ model public class ZZ {} */
//	
//	/*@ peer rep readonly */ Test1 t;
//	//@ model int m;
//	
////	int www; //@  maps t.t \into  m mmm ;
////	int www; //@  maps t. \into  m ;
////	int w3; //@  maps t.t \into   ;
////	int w5; //@  maps t ttt \into   ;
////	int w4; //@  maps ttt \into  m  ;
////
////	//@ \result ;
//	
//	//@ ensures \result == null;
//	public Boolean bn() {
//		//@ ghost \bigint b=0,bb;
//		//@ ghost peer rep readonly \real[][6] r;
//		//@ ghost \TYPE t;
//		//@ ghost \bigint bbb = b;
//		//@ ghost \bigint b4 = t;
//		//@ ghost int x,y,z;
//		return Boolean.TRUE;
//	}
//
////	int i = 0xg;
////	int kk = 0b0s ;
////	int k = 0b01010s01;
////	String s = "a\gn";
////	char ss = \u00aa0   ;
////	/*@ @@@*/
////	/*@ @@@*  /
////	/*@ @@@ */
////	/*@@@@@*/
////	/*@@@@ @@@*/
////	/*@ requires true; @@@@* 
////	/*@ requires true; @@@@ */
////	//@ ensures \\\\ ;
//	
//	//@ requires i < 15;
//	//@ ensures \result < 20;
//	public int m(int i) {
//		//@ assume i < 5;
//		i = i+1;
//		 lab:
//		i = i < 0 ? -i : i*2;
//		//@ assert i > \old(i);
//		if (i < 15) {
//			return -i;
//		} else {
//			//@ assert \old(i,lab) > 0;
//			return i + i;
//		}
//	}
//	
//	//@ public exceptional_behavior requires b;  signals (Exception e) true; signals (RuntimeException e) true;
//	//@ also
//	//@ public normal_behavior requires !b; ensures true;
//	public static void ex(boolean b) throws RuntimeException {
//		if (b) throw new RuntimeException();
//	}
//	
//	//@ public exceptional_behavior  requires true; signals (Exception e) true; diverges false;
//	public static void ex2() throws Exception {
//		throw new Exception();
//	}
//	
//	//@ requires k < 0;
//	//@ ensures true;
//	//@ also
//	//@ requires k > 0;
//	//@ ensures \result == 1;
//	public int mm() {
//		int i = 1;
//		try {
//			ex(true);
//			i = 0;
//		} catch (Exception e) {
//			//@ assert e != null;
//			i = 2;
//		}
//		return i;
//	}
//	
//	//@ ensures \result != 1;
//	//@ ensures i==2 ==> \result==1;
//	public int ms(int i) {
//		int k = 0;
//		switch(i-2) {
//		case 0:
//			k = 1;
//		case 1:
//			k = 2;
//			break;
//		default:
//			k=3;	
//		}
//		return k;
//	}
//	
//	static int sk;
//	int k;
//	
//	//@ modifies sk; 
//	public Test1() {
//	}
}
