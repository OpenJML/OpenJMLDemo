import org.jmlspecs.utils.*;

public class EntryPreconditionTest {

	@org.jmlspecs.annotation.SkipRac
	public static void main(String ... args) {
		//org.jmlspecs.utils.Utils.useExceptions = true;
		try {
			EntryPrecondition.m(0);
		} catch (JmlAssertionError.PreconditionEntry e) {
			// expected
			System.out.println("Correctly threw " + e.getClass() + " " + e.getLabel());
			System.out.println(e.getMessage());
		}
		try {
			EntryPrecondition.m(1);
		} catch (JmlAssertionError.PreconditionEntry e) {
			throw e; // not expected
		} catch (JmlAssertionError.Precondition e) {
			// expected
			System.out.println("Correctly threw " + e.getClass() + " " + e.getLabel());
			System.out.println(e.getMessage());
		}
		EntryPrecondition.m(2);
	}

}
