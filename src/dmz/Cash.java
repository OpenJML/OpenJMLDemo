/*
 * CSCI181F - Verification-Centric Software Engineering
 * Final
 * SOLUTIONS - DO NOT DISTRIBUTE
 */

package dmz;
 
/**
 * A class that represents a quantity of cash.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2013
 */
public class Cash {
  // Instance Fields
  
  /**
   * The amount of money represented by this Cash.
   */
  private final int my_amount; //@ in amount;
  //@ public model int amount;
  //@ private represents amount = my_amount;
  //@ public invariant 0 < amount;
  
  /**
   * A flag indicating whether this Cash has been loaded onto a gift card.
   */
  private boolean my_loaded;
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
  public Cash(final int the_amount) { // Default assignable for constructor is this.*, so without spec_public or in, my_loaded is not assignable
    my_amount = the_amount;
    my_loaded = false;
  }
  
  // Queries
  
  /**
   * @return How much money do you represent?
   */
  //@ ensures \result == amount;
  public int amount() {
    return my_amount;
  }
  
  /**
   * @return Have you been loaded onto a gift card?
   */
  //@ ensures \result == loaded;
  public boolean loaded() {
    return my_loaded;
  }
  
  // Commands
  
  /**
   * You have been loaded onto a gift card!
   */
  //@ requires !loaded;
  //@ ensures loaded;
  public void load() {
    my_loaded = true;
  }
}
