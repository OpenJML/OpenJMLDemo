public class BinarySearch {

	// binary search where the value sought is known to be in the array
	/*@  requires a.length >= 1;
	  @  requires (\forall int i; 0<i && i < a.length; a[i-1] <= a[i]);
	  @  requires (\exists int i; 0<=i && i < a.length; a[i] == value);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi - lo;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			//@ assume mid >= lo && mid < hi;
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid; 
			}
		}
		return lo;
	}

	// FIXME - find() above should not validate - if hi == lo+1 and value == a[hi] and value != a[lo],
	// then the above does not decrease hi-lo. Note that if the \exists requirement is removed, then
	// a warning is issued about the non-decreasing
	
	/*@  requires a.length >= 1;
	  @  requires (\forall int i; 0<i && i < a.length; a[i-1] <= a[i]);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find1(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi - lo;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			//@ assume mid >= lo && mid < hi;
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid; 
			}
		}
		return lo;
	}
	

	// Note - find2 validates and needs both the forall and exists preconditions
	// to do so. However, I'm surprised that this form of stating the quantifications
	// is sufficient for the prover, in the absence of induction
	/*@  requires a.length >= 1;
	  @  requires (\forall int i; 0<i && i < a.length; a[i-1] <= a[i]);
	  @  requires (\exists int i; 0<=i && i < a.length; a[i] == value);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find2(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi - lo;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			//@ assume mid >= lo && mid < hi;
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid+1; 
			}
		}
		return lo;
	}
	
	/*@  requires a.length >= 1;
	  @  requires (\forall int i,j; 0<=i && i<j && j < a.length; a[i] <= a[j]);
	  @  requires (\exists int i; 0<=i && i < a.length; a[i] == value);
	  @  requires a[0] <= value && value <= a[a.length-1]; // Redundant, but needed to establish the loop invariant
	  @  ensures a[\result] == value;
	 */
	public int find3(int[] a, int value) {
		int lo = 0;
		int hi = a.length -1;
		//@ loop_invariant 0<= lo && lo <= hi && hi < a.length && a[lo] <= value && value <= a[hi];
		//@ decreases hi - lo;
		while (lo < hi) {
			int mid = (lo + hi) / 2;
			//@ assume mid >= lo && mid < hi;
			if (a[mid] == value) return mid;
			if (value < a[mid]) {
				hi = mid;
			} else {
				lo = mid+1; 
			}
		}
		return lo;
	}
	

}
