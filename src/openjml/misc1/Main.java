public class Main {

	/*@ public invariant i > 0; */

	private/*@ spec_public */int i;

	/*@ ensures i > 0; */
	/*@ assignable \everything; */
	public Main() {
		i = 2;
	}
}

