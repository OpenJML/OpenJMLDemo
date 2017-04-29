
public class FirstTest2 {

	int a; //@ invariant a >= 0;
	
	//@ ensures a == 0;
	// @ assignable \nothing;
	// @ assignable \everything;
	// @ assignable this.*;
	FirstTest2() {
	  this.a = 0;
	}
	
	/*@ public normal_behaviour 
	   requires a >= 0;
       ensures this.a == a;
	   modifies this.a; @*/
	public void setA(int a) {
		this.a = a;
	}
	
}

class FirstTestSecond {
	public void maintest() {
		   FirstTest2 x = new FirstTest2();
		   //@ assert x.a == 0;
		   x.setA(10);
		}
}
