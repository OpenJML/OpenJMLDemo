package openjml.demo;


public class Types {
	
	
	public void types3(java.util.List<Integer> a) {
		/*@ nullable */ Integer i = a.get(0);
		//@ assert false;
	}
		
	public void types2(java.util.List<Integer> a) {
		//@ ghost boolean b1 = (\lbl A \type(Integer) <: \type(Number));  // true
		//@ ghost boolean b2 = (\lbl B \type(java.util.ArrayList<Integer>) <: \type(java.util.List<Integer>)); // true
		//@ ghost boolean b3 = (\lbl C \type(java.util.ArrayList<Integer>) <: \type(java.util.List<Number>));  // false
		//@ ghost boolean b4 = (\lbl D \type(java.util.ArrayList<Integer>) <: \type(java.util.List<?>));       // true
		//@ ghost boolean b5 = (\lbl E \type(java.util.ArrayList) <: \type(java.util.List));                   // true
		//@ assert false;
	}
		
	public <T> void types(java.util.List<T> a) {
		//@ assume \typeof(a) == \type(java.util.List<Integer>);
		//@ assert (\lbl A \type(T)) == (\lbl B \type(Integer));
		//@ assert (\lbl AA \erasure(\type(T))) == (\lbl BB \erasure(\type(Integer)));
		//@ assert (\lbl AAA \erasure(\type(T))) <: (\lbl BBB \erasure(\type(Integer)));
		//@ assert (\typeof(a)) <: (\type(Integer));
		//@ assert \erasure(\typeof(a)) <: \erasure(\type(Integer));
		/*@ nullable */ Integer i = (Integer)a.get(0);
	}
		
	public <T> void types4(java.util.List<T> a) {
		//@ assume \type(T) == \type(Integer);
		/*@ nullable */ Integer i = (Integer)a.get(0);
		//@ assert false;
	}
		
	public void types1(java.util.List<?> a) {
		//@ assume \typeof(a) == \type(java.util.List<Integer>);
		/*@ nullable */ Integer i = (Integer)a.get(0);
		//@ assert false;
	}
		
		
}
