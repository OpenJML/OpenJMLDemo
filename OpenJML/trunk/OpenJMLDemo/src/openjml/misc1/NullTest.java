/*
 * JML Demos
 * Fall 2013 CSCI181F
 * Daniel M. Zimmerman
 */

/**
 * A demonstration of the @nullable JML annotation.
 * 
 * @author Daniel M. Zimmerman
 * @version September 2013
 */
public class NullTest {
	
  public NullTest() { my_obj = null; }
  
  /**
   * A reference to some object.
   */
  protected Object my_obj;

  /**
   * @return the reference we're holding.
   */
  public Object getObj() { 
    return my_obj; 
  }

  /**
   * Sets the reference we're holding.
   * @param the_obj The new reference.
   */
  public void setObj(final Object the_obj) { 
     my_obj = the_obj; 
  }
  
  /**
   * The main method. Constructs a NullTest.
   * 
   * @param the_args Command line parameters, ignored.
   */
  public static void main(final String[] the_args) {
    final NullTest nt = new NullTest();
    System.out.println(nt);
  }
}