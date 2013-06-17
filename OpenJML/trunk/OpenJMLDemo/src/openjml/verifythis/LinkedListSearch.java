public class LinkedListSearch {

	public int head;
	public /*@ nullable */ List next;
	
	// Need to express that i is the index of the first element of the linked list
	// that is non-zero, otherwise i is the length of the list.
	
	// FIXME - how to even express this in JML?
	
	public int findZero() {
		LinkedListSearch jj = this;
		int i = 0;
		while (jj != null && jj.head != 0){
		  jj = jj.next;
		  i++;
		}
		return i;
	}
}
