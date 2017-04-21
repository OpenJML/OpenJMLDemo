//package sv_rac_solutions;

public class Queue {

    //@ public invariant 0 <= size && size <= arr.length;
    //@ public invariant 0 <= first && first < arr.length;
    //@ public invariant 0 <= next && next < arr.length;
    //@ public invariant first <= next ==> size == next - first;
    //@ public invariant first > next ==> size == next + arr.length - first;

    /*@ spec_public @*/ Object[] arr;
    /*@ spec_public @*/ int size;
    /*@ spec_public @*/ int first;
    /*@ spec_public @*/ int next;

	//@ public static final ghost int UNINITIALIZED = 0;
	//@ public static final ghost int EMPTY			= 1;
	//@ public static final ghost int NONEMPTY		= 2;
	//@ public static final ghost int FULL			= 3;

    //@ public instance ghost int status = UNINITIALIZED;
	
	/*@ public constraint \old(status) == UNINITIALIZED
	  @				==> ((status == EMPTY)    || (status == UNINITIALIZED));
	  @ public constraint \old(status) == EMPTY
	  @				==> ((status == NONEMPTY) || (status == EMPTY) ||
      @                                 (status == FULL));
	  @ public constraint \old(status) == NONEMPTY
	  @				==> ((status == NONEMPTY) || (status == EMPTY) || (status == FULL));
	  @ public constraint \old(status) == FULL
	  @				==> ((status == NONEMPTY) || (status == FULL)  ||
          @                                  (status == EMPTY));
	  @*/
    
    /*@ public invariant status == UNINITIALIZED || status == EMPTY ||
	  @			  status == NONEMPTY || status == FULL;
	  @*/
	
	/*@ requires 0 < max;
	  @ ensures arr.length == max;
	  @ ensures size == 0;
	  @ ensures status == EMPTY;
	  @*/
   Queue( int max ) {
	   arr   = new Object[max];
	   first = 0;
	   next  = 0;
	   size = 0;
	   //@ set status = EMPTY;
    }

    /*@ requires status != UNINITIALIZED;
      @ ensures \result == size;
      @ ensures status == \old(status);
      @*/
    public /*@pure */ int size() {
	  return size;
    }

    /*@ 
      @ requires status != UNINITIALIZED;
      @ requires size < arr.length;
      @ ensures arr[\old(next)] == x;
      @ ensures next == (\old(next) + 1) % arr.length;
      @ ensures first == \old(first);
      @ also
      @ requires (status == EMPTY || status == NONEMPTY);
      @ ensures (\old(size) < arr.length - 1) ? status == NONEMPTY : status == FULL;
      @*/   
    public void enqueue( Object x ) {
    	arr[next] = x;
    	next = (next + 1) % arr.length;
		//@ set status = size == arr.length - 1 ? FULL : NONEMPTY;
    	size++;
    }

    /*@ 
      @ requires status != UNINITIALIZED;
      @ requires size > 0;
      @ ensures \result == arr[\old(first)];
      @ ensures first == (\old(first) + 1) % arr.length;
      @ ensures next == \old(next);
      @ also
	  @ requires (status == NONEMPTY || status == FULL);
	  @ ensures  (\old(size) == 1) ? status == EMPTY : status == NONEMPTY;
	  @*/
    public Object dequeue() {
    	Object r = arr[first];
    	first = (first + 1) % arr.length;
	    //@ set status = size == 1 ?  EMPTY : NONEMPTY;
        size--;
    	return r;
    }
    
    public static void main(String[] args) {
    	Queue q = new Queue(10);
    	q.enqueue(new Object());
    	q.enqueue(new Object());
    	q.enqueue(new Object());
    	q.enqueue(new Object());
    	Object o = q.dequeue();
    	o = q.dequeue();
    	o = q.dequeue();
    }
}
