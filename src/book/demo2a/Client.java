public class Client {
	
	static Timer test(int h, int m) {
		Timer t = new Timer(h,m);
		t.tick();
		return t;
	}
}