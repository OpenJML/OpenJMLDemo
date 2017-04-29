public class Client {
	
	//@ requires m >= 0 && m <= 59 && h >= 0;
	static Timer test(int h, int m) {
		Timer t = new Timer(h,m);
		t.tick();
		return t;
	}
}