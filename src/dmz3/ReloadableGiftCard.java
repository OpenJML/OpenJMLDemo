/*
 * CSCI181F - Verification-Centric Software Engineering
 * Final
 * SOLUTIONS - DO NOT DISTRIBUTE
 */

package dmz3;
 
/**
 * A reloadable gift card.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2013
 */
public class ReloadableGiftCard extends GiftCard {
  // Constructor
  
  /**
   * Constructs a gift card with zero balance.
   */
  //@ ensures balance == 0;
  //@ assignable balance;
  public ReloadableGiftCard() {
    super();
  }
  
  /**
   * Constructs a gift card loaded with the specified cash.
   * 
   * @param the_cash The cash to load.
   */
  //@ requires !the_cash.loaded;
  //@ ensures balance == the_cash.amount;
  //@ ensures the_cash.loaded;
  //@ assignable balance, the_cash.loaded;
  public ReloadableGiftCard(final Cash the_cash) {
    super(the_cash);
  }
  
  // Commands
  
  /**
   * Load the_cash onto yourself!
   * 
   * @param the_cash The cash.
   */
  //@ requires !the_cash.loaded;
  //@ requires balance() + the_cash.amount() <= Integer.MAX_VALUE;
  //@ ensures balance == \old(balance) + the_cash.amount;
  //@ ensures the_cash.loaded;
  //@ assignable balance, the_cash.loaded;
  public void load(final Cash the_cash) {
    setBalance(balance() + the_cash.amount());
    the_cash.setLoaded();
  }
}