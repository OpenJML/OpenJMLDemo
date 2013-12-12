/*
 * CSCI181F - Verification-Centric Software Engineering
 * Final
 * SOLUTIONS - DO NOT DISTRIBUTE
 */

package dmz2;
 
/**
 * A reloadable gift card that can also have cash withdrawn from it;
 * essentially, a debit card associated with a particular merchant.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2013
 */
public class DebitCard extends ReloadableGiftCard {
  // Instance Fields
  
  /**
   * The most recently converted Cash.
   */
  private /*@ nullable */ Cash my_last_cash; //@ in last_cash, converted;
  //@ public model nullable Cash last_cash;
  //@ private represents last_cash = my_last_cash;
  //@ public model boolean converted;
  //@ private represents converted = (my_last_cash != null);
  
  
  // Constructor
  
  /**
   * Constructs a debit card with zero balance.
   */
  //@ ensures balance == 0;
  //@ ensures !converted;
  //@ assignable balance, last_cash;
  public DebitCard() {
    super();
    my_last_cash = null;
  }
  
  /**
   * Constructs a debit card loaded with the specified cash.
   * 
   * @param the_cash The cash to load.
   */
  //@ requires !the_cash.loaded;
  //@ ensures balance == the_cash.amount;
  //@ ensures the_cash.loaded;
  //@ ensures !converted;
  //@ assignable balance, last_cash, the_cash.loaded;
  public DebitCard(final Cash the_cash) {
    super(the_cash);
    my_last_cash = null;
  }
  
  // Queries
  
  /**
   * @return Have you ever converted any of your balance to cash?
   */
  //@ ensures \result == converted;
  public boolean converted() {
    return my_last_cash != null;
  }
  
  /**
   * @return What is your most recently converted cash?
   */
  //@ requires converted;
  //@ ensures \result == last_cash;
  public Cash lastCash() {
    return my_last_cash;
  }
  
  // Commands
  
  /**
   * Convert the_amount of your balance into cash!
   * 
   * @param the_amount The amount to convert.
   */
  //@ requires the_amount <= balance;
  //@ ensures balance == \old(balance) - the_amount;
  //@ ensures converted;
  //@ ensures \fresh(last_cash);
  //@ ensures last_cash.amount == the_amount;
  //@ assignable balance, last_cash;
  public void convert(final int the_amount) {
    my_last_cash = new Cash(the_amount);
    setBalance(balance() - the_amount);
  }
}
