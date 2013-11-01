/*
 * Extended Static Checking Exercise
 * Fall 2013 CSCI181F - Verification-centric Software Engineering
 * Daniel M. Zimmerman
 */



/**
 * A class that represents a quantity of (U.S.) cash in dollars 
 * and cents. The quantity can be positive or negative (representing
 * an asset or a debt). Instances of this class are immutable, so it has
 * only queries (and a constructor).
 * 
 * @author Daniel M. Zimmerman
 * @version 2013-10-17
 */
public class CashAmountMutable {
  
  // invariants for sane amounts of dollars and cents
  //@ public invariant -CENTS_IN_DOLLAR < my_cents && my_cents < CENTS_IN_DOLLAR;
  // @ public invariant my_dollars > 0 <==> my_cents >= 0;
  // @ public invariant my_dollars <= 0 <==> my_cents <= 0;
	  //@ public invariant my_dollars > 0 ==> my_cents >= 0 && my_cents > 0 ==> my_dollars >= 0;
	  //@ public invariant my_dollars < 0 ==> my_cents <= 0 && my_cents < 0 ==> my_dollars <= 0;
  
  /**
   * The number of cents in one dollar.
   */
  public static final int CENTS_IN_DOLLAR = 100;
  
  /**
   * The number of dollars.
   */
  private /*@ spec_public */ int my_dollars;
  
  /**
   * The number of cents.
   */
  private /*@ spec_public */ int my_cents;
  
  //@ requires -100 < the_cents && the_cents < 100;
  //@ requires the_cents <= 0 <==> the_dollars <= 0;
  //@ requires the_cents >= 0 <==> the_dollars >= 0;
  //@ assignable \everything;
  /**
   * Constructs a new CashAmount representing the specified amount of cash.
   * 
   * @param the_dollars The number of dollars.
   * @param the_cents The number of cents.
   */
  public CashAmountMutable(final int the_dollars, final int the_cents) {
    my_dollars = the_dollars;
    my_cents = the_cents;
  }

  /**
   * @return a new CashAmount representing the negation of this
   * CashAmount.
   */
  public CashAmountMutable negate() {
    return new CashAmountMutable(-my_dollars, -my_cents);
  }
  
  /**
   * Increases this CashAmount by the specified CashAmount.
   * 
   * @param the_amount The amount to increase by.
   * @return The resulting CashAmount.
   */
  //@ ensures \result.my_dollars*100 + \result.my_cents == (the_amount.my_dollars*100 + the_amount.my_cents) + \old(my_dollars*100+my_cents);
  public CashAmountMutable increase(final CashAmountMutable the_amount) {
	    int new_dollars = my_dollars + the_amount.my_dollars;
	    int new_cents = my_cents + the_amount.my_cents;
	    
	    if (new_cents <= -CENTS_IN_DOLLAR) {
	      new_cents = new_cents + CENTS_IN_DOLLAR;
	      new_dollars = new_dollars - 1;
	    } 
	    if (new_cents >= CENTS_IN_DOLLAR) {
	      new_cents = new_cents - CENTS_IN_DOLLAR;
	      new_dollars = new_dollars + 1;
	    } 
	    if (new_cents < 0 && new_dollars > 0) { 
	      new_cents = new_cents + CENTS_IN_DOLLAR; 
	      new_dollars = new_dollars - 1;
	    } 
	    if (new_cents > 0 && new_dollars < 0) {
	      new_cents = new_cents - CENTS_IN_DOLLAR; 
	      new_dollars = new_dollars + 1;
	    }
	    
	    return new CashAmountMutable(new_dollars, new_cents);
	  }

  //@ requires this != the_amount;
  //@ ensures my_dollars*100 + my_cents == (the_amount.my_dollars*100 + the_amount.my_cents) + \old(my_dollars*100+my_cents);
  public void add(final CashAmountMutable the_amount) {
	    int new_dollars = my_dollars + the_amount.my_dollars;
	    int new_cents = my_cents + the_amount.my_cents;
	    
	    //@ ghost boolean same = (\lbl SAME (this == the_amount));
	    if (new_cents <= -CENTS_IN_DOLLAR) {
	      new_cents = new_cents + CENTS_IN_DOLLAR;
	      new_dollars = new_dollars - 1;
	    } 
	    if (new_cents >= CENTS_IN_DOLLAR) {
	      new_cents = new_cents - CENTS_IN_DOLLAR;
	      new_dollars = new_dollars + 1;
	    } 
	    if (new_cents < 0 && new_dollars > 0) { 
	      new_cents = new_cents + CENTS_IN_DOLLAR; 
	      new_dollars = new_dollars - 1;
	    } 
	    if (new_cents > 0 && new_dollars < 0) {
	      new_cents = new_cents - CENTS_IN_DOLLAR; 
	      new_dollars = new_dollars + 1;
	    }
	    
	    my_dollars = new_dollars;
	    my_cents = new_cents;
	  }
	  
  /**
   * Decreases this CashAmount by the specified CashAmount.
   * 
   * @param the_amount The amount to decrease by.
   * @return The resulting CashAmount.
   */
  public CashAmountMutable decrease(final CashAmountMutable the_amount) {
    return increase(the_amount.negate());
  }
    
  /**
   * @return The number of dollars in this CashAmount.
   */
  public /*@ pure helper */ int dollars() {
    return my_dollars;
  }
  
  /**
   * @return The number of cents in this CashAmount.
   */
  public /*@ pure helper */ int cents() {
    return my_cents;
  }
  
  /**
   * Compare this CashAmount with the specified CashAmount for equivalence.
   * Equivalence here means "has exactly the same numbers of dollars and cents."
   * 
   * @param the_other The other CashAmount.
   * @return true if the two amounts are equivalent, false otherwise. 
   */
  public boolean equivalent(final CashAmountMutable the_other) {
    return the_other.my_dollars == my_dollars && the_other.my_cents == my_cents;  
  }
  
//  /**
//   * Compare this object with another for equivalence.
//   * 
//   * @param the_other The other object.
//   * @return true if the objects are equivalent, false otherwise.
//   */
//  public boolean equals(final Object the_other) {
//    boolean result = false;
//    
//    if (this == the_other) {
//      result = true;
//    } else if (the_other != null && the_other.getClass() == getClass()) {
//      final CashAmount other_cash = (CashAmount) the_other;
//      result = other_cash.my_dollars == my_dollars && 
//               other_cash.my_cents == my_cents;
//    }
//    
//    return result;
//  }
//
//  /**
//   * @return a hash code for this CashAmount
//   */
//  public int hashCode() {
//    return my_dollars * CENTS_IN_DOLLAR + my_cents;
//  }
}
