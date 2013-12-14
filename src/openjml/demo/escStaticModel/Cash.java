/*
 * CSCI181F - Verification-Centric Software Engineering
 * Final
 * SOLUTIONS - DO NOT DISTRIBUTE
 */

package escStaticModel;
 
/**
 * A class that represents a quantity of cash.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2013
 */
public class Cash {
  // Static Fields
  
  /**
   * The total amount of outstanding cash.
   */
  private static int _total_cash; //@ in total_cash;
  //@ public static model int total_cash;
  //@ private static represents total_cash = _total_cash;
  
  // Instance Fields
  
  /**
   * The amount of money represented by this Cash.
   */
  private final int my_amount; //@ in amount;
  //@ public model int amount;
  //@ private represents amount = my_amount;
  //@ public invariant 0 < amount;
  
  /**
   * A flag indicating whether this Cash has been loaded onto a card.
   */
  private boolean my_loaded; //@ in loaded;
  //@ public model boolean loaded;
  //@ private represents loaded = my_loaded;
  //@ public constraint \old(loaded) ==> loaded;

  // Constructor
  
  /**
   * Constructs a Cash representing the specified amount of money.
   * 
   * @param the_amount The amount of money to represent.
   */
  //@ requires 0 < the_amount;
  //@ ensures amount == the_amount;
  //@ ensures !loaded;
  //@ ensures total_cash == \old(total_cash) + the_amount;
  //@ assignable amount, loaded, total_cash;
  public Cash(final int the_amount) {
    my_amount = the_amount;
    my_loaded = false;
    _total_cash = _total_cash + the_amount;
  }
  
  // Queries
  
  /**
   * @return How much money do you represent?
   */
  //@ ensures \result == amount;
  public /*@ pure */ int amount() {
    return my_amount;
  }
  
  /**
   * @return Have you been loaded onto a card?
   */
  //@ ensures \result == loaded;
  public /*@ pure */ boolean loaded() {
    return my_loaded;
  }
  
  // Commands
  
  /**
   * You have been loaded onto a card!
   */
  //@ requires !loaded;
  //@ ensures loaded;
  //@ assignable loaded;
  public void setLoaded() {
    my_loaded = true;
  }
}
