package openjml.test;
import openjml.testa.TestX;

public class TestY extends TestX {
	TestX t;
	
	
	//@ protected normal_behavior
	//@ requires apr == 0 && t.mpr();
	//@ requires apa == 0 && t.mpa();
	//@ requires apt == 0 && mpt() && t.mpt();
	//@ requires apb == 0;
	public void m() {
		//@ assert t.apr == 0;
		//@ assert t.apa == 0;
		//@ assert t.apt == 0 && apt == 0;
		//@ assert t.apb == 0;
		
		mpt();
		//t.mpt();
	}
}
