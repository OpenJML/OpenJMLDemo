public class Z {
	
	public static void main(String ... args) {
		short i = 9;
		short j = 7;
		short k = (short) (i + j);
		k += i;
		k = (short)(k + j);
		System.out.println(k);
	}
	
}