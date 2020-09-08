/*
 * CSCI181F - Verification-Centric Software Engineering
 * Final
 * SOLUTIONS - DO NOT DISTRIBUTE
 */

package dmz3;
 
/**
 * A gift card that can be used for only one purchase.
 * 
 * @author Daniel M. Zimmerman
 * @version December 2013
 */
public class SingleUseGiftCard extends GiftCard {
  // Instance Fields
  
  /**
   * A flag indicating whether this gift card has been used.
   */
  private boolean my_used; //@ in used;
  //@ public model boolean used;
  //@ private represents used = my_used;
  //@ public constraint \old(used) ==> used;
  
  // Constructor
  
  /**
   * Constructs a gift card loaded with the specified cash.
   * 
   * @param the_cash The cash to load.
   */
  //@ requires !the_cash.loaded;
  //@ ensures balance == the_cash.amount;
  //@ ensures the_cash.loaded;
  //@ ensures !used;
  //@ assignable balance, the_cash.loaded;
  public SingleUseGiftCard(final Cash the_cash) {
    super(the_cash);
    my_used = false;
  }
  
  // Queries

  /**
   * Checks to see if the gift card can be used to make a purchase.
   * A single use gift card can only be used if it hasn't yet
   * been used.
   * 
   * @return Can you be used to make a purchase of the_amount?
   */
  //@ also ensures \result <==> !used;
  @Override
  public /*@ pure */ boolean canUseForPurchase() {
    return !my_used;
  }
}