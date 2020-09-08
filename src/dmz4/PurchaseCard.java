package dmz4;

/**
 * A card that can be used to make purchases.
 * @author Jeb Brooks
 * @version 12/16/13
 */
public class PurchaseCard {
  
  /**
   * The balance of the card.
   */
  protected int my_balance; //@ in balance;
  //@ public model int balance;
  //@ private represents balance = my_balance;
  
  /**
   * The purchase status of the card.
   */
  protected boolean my_can_purchase; //@ in purchase;
  //@ public model boolean purchase;
  //@ private represents purchase = my_can_purchase;
  
  // Invariants and Constraints
  //@ public invariant balance >= 0;
  
  /*@ ensures balance == 0;
      ensures purchase;
      assignable balance, purchase;
   */
  /**
   * You are a purchase card with a zero balance.
   */
  public PurchaseCard() {
    my_balance = 0;
    my_can_purchase = true;
  }
  
  /*@ requires !the_initial_cash.loaded;
      ensures the_initial_cash.loaded;
      ensures balance == the_initial_cash.getAmount();
      ensures purchase;
      assignable balance, purchase, the_initial_cash.loaded;
   */ 
  /**
   * You are a purchase card with the_initial_cash.
   * @param the_initial_cash the initial value to load
   */
  public PurchaseCard(final Cash the_initial_cash) {
    my_balance = the_initial_cash.getAmount();
    the_initial_cash.load();
    my_can_purchase = true;
  }
  
  //@ ensures \result == balance;
  //@ pure;
  /**
   * What is your balance?
   * @return the balance of this card.
   */
  public int getBalance() {
    return my_balance;
  }
  
  //@ ensures \result == purchase;
  //@ pure;
  /**
   * Can you be used to make a purchase?
   * @return true if this card can make a purchase.
   */
  public boolean canPurchase() {
    return my_can_purchase;
  }
}
