package openjml.demo;


public class Types {
	
	
	public void types3(java.util.List<Integer> a) {
		/*@ nullable */ Integer i = a.get(0);
		//@ assert false; // ERROR
	}
		
	public void types2(java.util.List<Integer> a) {
		//@ ghost boolean b1 = (\lbl A \type(Integer) <: \type(Number));// true
		//@ ghost boolean b2 = (\lbl B \type(java.util.ArrayList<Integer>) <: \type(java.util.List<Integer>)); // true
		//@ ghost boolean b3 = (\lbl C \type(java.util.ArrayList<Integer>) <: \type(java.util.List<Number>)); // false
		//@ ghost boolean b5 = (\lbl E \erasure(\type(java.util.ArrayList)) <: \erasure(\type(java.util.List))); // true
		//@ assert b1 && b2 && !b3 && b5; 
		//@ assert false; // To be sure of feasibility and so that labels are printed
	}
		
	public <T> void types(java.util.List<T> a) {
		//@ assume \typeof(a) == \type(java.util.List<Integer>);
		/*@ nullable */ T t = a.get(0);
		/*@ nullable */ Integer i = (Integer)t;
	}
		
	public <T> void types5(java.util.List<T> a) {
		//@ assume \type(java.util.List<T>) == \type(java.util.List<Integer>);
		//@ assert \type(T) == \type(Integer);
		/*@ nullable */ Integer i = (Integer)a.get(0);
	}
		
	public <T> void types4(java.util.List<T> a) {
		//@ assume \type(T) == \type(Integer);
		/*@ nullable */ Integer i = (Integer)a.get(0);
	}
		
	public void types1(java.util.List<?> a) {
		//@ assume \typeof(a) == \type(java.util.List<Integer>);
		/*@ nullable */ Integer i = (Integer)a.get(0); // ERROR - a ? is not necessarily an Integer
	}
		
	public int typesr(java.util.List<?> a) {
		return a.size();
	}
		
	public /*@ nullable */ <T> T typesz(java.util.List<T> a) {
		return a.get(0);
	}
		
		
}
