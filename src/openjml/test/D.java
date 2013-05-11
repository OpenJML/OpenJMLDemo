package openjml.test;

import java.util.LinkedList;
import java.util.List;

public class D {

	  public static void main(String[] args) {
		  //System.out.println("START");
		  LinkedList<Integer> i = new LinkedList<Integer>();
		  LinkedList<? extends Object> a = i;
		  LinkedList<Integer> b = (LinkedList<Integer>)a;
		  LinkedList<Boolean> c = (LinkedList<Boolean>)a; // SHould get an error
		  c.add(new Boolean(true));
		  //b.add(new Integer(1));
		  Integer x = i.get(0);
		  System.out.println(x);
		  //System.out.println("END");
	  }


}
