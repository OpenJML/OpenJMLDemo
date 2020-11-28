public class MaxByElimination {

  //@ requires a != null && a.length > 0;
  //@ ensures 0 <= \result < a.length;
  //@ ensures (\forall int i; 0 <= i < a.length; a[i] <= a[\result]);
  public static int max(int[] a) {
    int x = 0;
    int y = a.length-1;

    //@ loop_invariant 0 <= x <= y < a.length;
    // So far either a[y] is the largest or a[x] is the largest of everything beyond x and beyond y (not including a[x] and a[y])
    /*@ loop_invariant ((\forall int i; 0<=i && i<x; a[i] <= a[y]) && (\forall int i; y < i && i < a.length; a[i] <= a[y]))
	               ||  ((\forall int i; 0<=i && i<x; a[i] <= a[x]) && (\forall int i; y < i && i < a.length; a[i] <= a[x]));
     */	
    //@ decreases y-x;
    while (x != y) {
      if (a[x] <= a[y]) x++;
      else y--;
    }
    return x;
  }
}
