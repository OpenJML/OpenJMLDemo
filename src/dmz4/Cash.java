package dmz4;

/**
 * A representation of a quantity of money.
 * @author Jeb Brooks
 * @version 12/16/13
 */
public class Cash {
  /**
   * The amount of money this represents.
   */
  private final int my_amount; //@ in amount;
  //@ public model int amount;
  //@ private represents amount = my_amount;
  
  /**
   * If the Cash has been loaded onto a card.
   */
  private boolean my_loaded; //@ in loaded;
  //@ public model boolean loaded;
  //@ private represents loaded = my_loaded;
  
  /*
   * Constraints and Invariants
   */
  
  // Once loaded onto a card a cash always reports it has been loaded onto a card.
  //@ public constraint \old(loaded) ==> loaded;
  
  // Cash objects are immutable amounts
  //@ public constraint \old(amount) == amount;
  
  // Cash objects are positive integral amounts
  //@ public invariant amount > 0;
 
  /*@ requires the_amount > 0;
      ensures amount == the_amount;
      ensures loaded == false;
      assignable amount, loaded;
   */
  /**
   * Create a Cash object.
   * @param the_amount the value of the cash object
   */
  public Cash(final int the_amount) {
    my_amount = the_amount;
    // Start not used.
    my_loaded = false;
  }
  
  //@ ensures \result == amount;
  //@ pure;
  /**
   * How much money do you represent?
   * @return the amount of money this Cash represents
   */
  public int getAmount() {
    return my_amount;
  }
  
  //@ ensures \result == loaded;
  //@ pure;
  /**
   * Have you been loaded onto a card?
   * @return if the cash has been loaded onto a card
   */
  public boolean isLoaded() {
    return my_loaded;
  }
  
  /*@ requires !loaded;
      ensures loaded;
      assignable loaded;
   */
  /**
   * You have been loaded onto a card!
   */
  public void load() {
    my_loaded = true;
  }
}
