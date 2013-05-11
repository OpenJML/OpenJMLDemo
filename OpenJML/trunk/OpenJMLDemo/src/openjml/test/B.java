package openjml.test;
import java.util.*;

public class B {

//  static int j,k;
//
//  //@ requires i > 0;
//  //@ modifies j;
//  //@ ensures j == i;
//  public void setj(int i) {
//    synchronized(this) {
//    	j = i;
//        int[] a = new int[-1];
//    }
//  }
  
  public static void z() {
	  Integer i = 5;
	  int j = i;
	  //@ ghost boolean b = (\forall int ii,jj; ii < 10; jj < 10);
  }
  
//  public static void m() {
//	  Object[] a = new String[3];
//	  a[0] = new Integer(0); // FIXME - should get an error
//  }
//
//  public void n() {
//	  /*@ non_null*/List<? extends Object> a = new LinkedList<Integer>();
//	  /*@ nullable */ LinkedList<Integer> b = (LinkedList<Integer>)a;
//	  /*@ nullable */ LinkedList<Boolean> c = (LinkedList<Boolean>)a; // SHould get an error
//	  c.add(new Boolean(true));
//	  b.add(new Integer(1));
//  }
//
//  //@ ensures j == 1;
//  public static void main(String[] args) {
//    (new B()).setj(0);
//  }
//  
//  public static void p() {
//	  /*@ non_null*/ Object i = new Integer(0);
//	  Boolean b = (Boolean)i;
//  }
//
//  public static Integer q() {
//	  /*@ non_null*/ Object i = new Integer(0);
//	  Integer b = (Integer)i; // FIXME - casts retain nullness
//	  return b;
//  }

}