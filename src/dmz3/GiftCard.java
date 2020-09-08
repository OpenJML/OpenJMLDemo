/*
 * CSCI181F - Verification-Centric Software Engineering
 * Final
 * SOLUTIONS - DO NOT DISTRIBUTE
 */

package dmz3;
 
/**
 * A gift card that can be used to make purchases.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2013
 */
public class GiftCard {
  // Instance Fields
  
  /**
   * The balance on this gift card.
   */
  private int my_balance; //@ in balance;
  //@ public model int balance;
  //@ private represents balance = my_balance;
  //@ public invariant 0 <= balance;

  // Constructor
  
  /**
   * Constructs a gift card with zero balance.
   */
  //@ ensures balance == 0;
  //@ pure
  public GiftCard() {
    my_balance = 0;
  }
  
  /**
   * Constructs a gift card loaded with the specified cash.
   * 
   * @param the_cash The cash to load.
   */
  //@ requires !the_cash.loaded;
  //@ ensures balance == the_cash.amount;
  //@ ensures the_cash.loaded;
  //@ assignable the_cash.loaded;
  public GiftCard(final Cash the_cash) {
    my_balance = the_cash.amount();
    the_cash.setLoaded();
  }
  
  // Queries
  
  /**
   * @return What is your balance?
   */
  //@ ensures \result == balance;
  public /*@ pure */ int balance() {
    return my_balance;
  }
  
  /**
   * @return Can you be used to make a purchase?
   */
  public /*@ pure */ boolean canUseForPurchase() {
    return true;
  }
  
  // Commands
  
  /**
   * Make a purchase of the_amount!
   * 
   * @param the_amount The amount.
   */
  //@ requires 0 < the_amount && the_amount <= balance;
  //@ requires canUseForPurchase();
  //@ ensures balance == \old(balance) - the_amount;
  public void purchase(final int the_amount) {
    my_balance = my_balance - the_amount;
  }
  
  /**
   * Absorb the balance of the_other_card!
   * 
   * @param the_other_card The other card.
   */
  //@ requires the_other_card != this;
  //@ requires balance() + the_other_card.balance() <= Integer.MAX_VALUE;
  //@ ensures balance == \old(balance + the_other_card.balance);
  //@ ensures the_other_card.balance == 0;
  //@ assignable balance, the_other_card.balance;
  //@ also
  //@ requires the_other_card == this;
  //@ ensures balance == \old(balance);
  public void absorb(final GiftCard the_other_card) {
    if (the_other_card != this) {
      setBalance(balance() + the_other_card.balance());
      the_other_card.setBalance(0);
    }
  }
  
  /**
   * Sets the balance on this gift card; for use by child classes.
   * 
   * @param the_balance The new balance.
   */
  //@ requires 0 <= the_balance;
  //@ ensures balance == the_balance;
  //@ assignable balance;
  protected void setBalance(final int the_balance) {
    my_balance = the_balance;
  }
}