package openjml.test;

public class Trace {
	public int f;
	public int[] a;
	static public int ss;
	static Trace t;
	
	//@ requires i > 0;
	//@ ensures ss > 0;
	public void m(int i) {
		//@ assume a.length > 4;
		ss = 57;
		int k = i + 5 -1;
		int kk = k + k; 
		switch (kk) {
		case 1: 
			k = 3; break;
		case 13:
			k = 7; break;
		default:
			k = 9;
		
		}
		if (kk == 12) {
			kk += 2;
		} else {
			kk = kk -  2;
		}
		try {
			k = 7;
			throw new RuntimeException();
		} catch (Exception e) {
			k = 8;
		} finally {
			k = 9;
		}
		Trace.ss = this.ss + 1;
		k = Trace.ss++;
		k = --Trace.ss;
		k = 15 + mm(7);
		ms(8);
		k = kk - 5;
		this.f = 7;
		this.f += 1;
		f = f + 9;
		f += 1;
		this.a[1] = 19;
		a[2] = a[1] + 7;
		a[2] += 1;
		//@ assert k != 7 <== true;
	}
	
	//@ requires k > 0;
	//@ ensures \result == k;
	static int mm(int k) {
		return k;
	}
	
	//@ requires k > 0;
	//@ ensures false;
	static void ms(int k) {
		//@ assume t != null;
		//@ assume t.a.length > 2;
		if (k >= 0) {
			// @ assume k<0;
			int i = k;
			++i;
			i = t.a[0];
			t.a[0]++;
			i = t.a[0];
			++t.a[0];
			i = ss;
			ss++;
			i = ss;
			++ss;
			ss+=1;
			t.a[0]+=1;
			t.f+=1;
			//@ assert k>=0;
		} else {
			// @ assume k >= 0;
		}
	}
}
