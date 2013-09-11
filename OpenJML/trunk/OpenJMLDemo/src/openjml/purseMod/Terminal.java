

import java.util.Random;

class Terminal {

	//private 
	/*@ spec_public */ byte pin[]=new byte[8];
	//@ public invariant pin.length == 8;
	//private 
	/*@ spec_public */ int pin_pos=0;
	// private 
	Random random=new Random(0);
	// private 
	/*@ spec_public */ int ownerid;
	// private 
	/*@ spec_public nullable */ Card card;

	// invariants and constraints on fields
	/*@ public invariant pin != null;
   
       // pin never changes
       public constraint pin.length == \old(pin.length);
      
       // all elements in pin between 0 and pin_pos are digits 
       public invariant (\forall int i; 0 <= i && i < pin_pos; 0 <= pin[i] && pin[i] <= 9);  
       public invariant (\forall int i; pin_pos <= i && i < pin.length; pin[i] == -1);  
      
       // pin_pos always points to position within the pin code
       public invariant 0 <= pin_pos && pin_pos <= pin.length;
   
	 */
  
	// life cycle of the terminal
	// the terminal can be either empty or filled
	// if the terminal is filled with an uninitialised card, 
	// the user has to enter 8 digits, and then call initCard to initialise the card
  
	// if the terminal is filled with a initialised card, then the card operations 
	// (load, pay, unlock and balance) can be applied - provided the card is in the 
	// appropriate state
  
	// clearPin() and enterDigit(digit) can always be called

	/*@ public static final ghost int EMPTY = 0;
        public static final ghost int FILLED_UNINIT = 1;
        public static final ghost int FILLED_INIT = 2;
        public static final ghost int FILLED_READYFORINIT = 3;
           
           // FIXME - should be automatic for final variables
        public static invariant EMPTY==0 && FILLED_UNINIT==1 && FILLED_INIT==2 && FILLED_READYFORINIT==3;
        
        public ghost int status = EMPTY;
        

        // possible values status
        public invariant status == EMPTY || status == FILLED_UNINIT || status == FILLED_INIT ||
                  status == FILLED_READYFORINIT;
   
        // constraints describing the transition system               
        public constraint \old(status) == EMPTY ==>
                      status == EMPTY || status == FILLED_UNINIT || status == FILLED_READYFORINIT ||
                      status == FILLED_INIT;
        public constraint \old(status) == FILLED_UNINIT ==>
                      status == FILLED_UNINIT || status == FILLED_READYFORINIT || status == EMPTY;
        public constraint \old(status) == FILLED_INIT ==>
                      status == FILLED_INIT || status == EMPTY;
        public constraint \old(status) == FILLED_READYFORINIT ==>
                      status == FILLED_READYFORINIT || status == FILLED_INIT || status == EMPTY;

            
        //consistency requirements on the state
        public invariant card == null <==> status == EMPTY;
        public invariant status == FILLED_UNINIT <==> 
                     card != null && card.status == Card.UNINIT && pin_pos < pin.length;
        public invariant status == FILLED_READYFORINIT <==> 
                     card != null && card.status == Card.UNINIT && pin_pos == pin.length;
        public invariant status == FILLED_INIT <==> 
                     card != null && card.status != Card.UNINIT;
	 */ 

  
	/*@ ensures (\forall int i; 0 <= i && i < pin.length; pin[i] == -1);
        ensures pin_pos == 0;
        ensures status == EMPTY;

        assignable this.ownerid, pin[*], status;
        signals (Exception) false;
	 */
	public Terminal(int ownerid){
		this.ownerid=ownerid;
		/*@ loop_invariant i>=0 && i<=pin.length && (\forall int j; j>=0 && j<i; pin[j] == -1); */
		for(int i=0;i<pin.length;i++) pin[i]=-1;
		//@ set status = EMPTY;
	}
  
	// insert card
	// status of the card determines status of the terminal
	// method will not throw an exception
	
	// note: changed order of instructions, so that invariants on terminal status are valid upon entry and exit
	// of clearPin()
	/*@ requires card != null;
        requires status == EMPTY;
        assignable this.card, this.pin_pos, this.pin[*], this.status;
        ensures this.card == card;
        ensures card.status == Card.UNINIT ==> status == FILLED_UNINIT;
        ensures card.status != Card.UNINIT ==> status == FILLED_INIT;
        signals (Exception) false;
	 */
	public void insertCard(Card card){
		clearPin();
		this.card=card;
		// pin_pos is always 0 after clearPin()
		//@ set status = (card.status == Card.UNINIT ? FILLED_UNINIT : FILLED_INIT);
	}
  
	// digit at position pin_pos is changed to digit, all other elements in pin remain unchanged
	// if the card still is uninitialised, and a sufficient number of digits has been entered, then the 
	// status is changed to FILLED_READYFORINIT
	// method will not throw an exception
	/*@ requires 0 <= digit && digit <= 9;
        requires pin_pos < pin.length;
        requires card != null;
        assignable pin_pos, pin[pin_pos], status;
        ensures (\forall int i; 0 <= i && i < pin.length; 
                       i == \old(pin_pos)? pin[i] == digit : pin[i] == \old(pin[i]));
        ensures pin_pos == \old(pin_pos) + 1;
        ensures status == (\old(status) == FILLED_UNINIT && pin_pos == pin.length ? 
                              FILLED_READYFORINIT : 
                              \old(status));
        signals (Exception) false;
	 */
	public void enterDigit(byte digit){
		pin[pin_pos]=digit;
		pin_pos++;
		/*@ set status = 
		       (status == FILLED_UNINIT && pin_pos == pin.length ? FILLED_READYFORINIT : 
		       (status == FILLED_UNINIT && pin_pos < pin.length ? FILLED_UNINIT : FILLED_INIT));
		*/
	}

	// all entries in pin are set to -1, and pin_pos is reset to 0
	// status is unchanged
	// method will not throw an exception
	

	/*@ requires pin_pos == pin.length;
	    assignable pin_pos, pin[*];
	    ensures (\forall int i; 0 <= i && i < pin.length; pin[i] == -1);
        ensures pin_pos == 0;
        ensures status == \old(status);
      	signals (Exception) false;
	 */
	public void clearPin(){
		//@ loop_invariant pin_pos >=0 && (\forall int i; pin_pos<=i && i<\old(pin_pos); pin[i]==-1);
		while(pin_pos>0){
			pin_pos--;
			pin[pin_pos]=-1;
			// error 6
			// fix 6: pin_pos--;
		}
	}

	// method can only be called when terminal is empty
	// removes card from the terminal
	// method will not throw an exception
	/*@ requires status != EMPTY;
        ensures status == EMPTY;
        signals (Exception) false;
	 */ 
	public void ejectCard(){
		card = null;
		//@ set status = EMPTY;
	}

	// can only be called when terminal contains an initialised card (that is still active)
	// does not change status of terminal
	// method cannot throw an exception, because the token has just been signed, so it will pass the check in method
	// load on card
	/*@ requires status == FILLED_INIT;
        requires card.status == Card.ACTIVE;
      	ensures status == \old(status);
       	signals (Exception) false;
	 */
	public void load(int amount) throws CardException {
		/* normally, we would get a bank account number from the card
    	   and use the pin to obtain a token from the bank. However,
    	   for the sake of simplicity, we just create a good token.
    	   */
		Token tok=new Token(amount,card.getCardID(),random.nextInt());
		tok.sign(12944557,254557);
		card.load(tok);
	}
  
	// can only be called when terminal contains an initialised card (that is still active)
	// does not change status of terminal
	// method can throw an exception if the current pin code is not the basic pin code
	/*@ requires status == FILLED_INIT;
	    requires card.status == Card.ACTIVE;
	    ensures status == \old(status);
	    signals_only CardException;
	    signals (CardException) 
	       status == \old(status) &&
	       (\exists int i; 0 <= i && i < card.basic_pin.length; pin[i] != card.basic_pin[i]); 
	 */
	public void pay(int amount) throws CardException {
		Token tok=card.pay(amount,ownerid,pin);
		// Deposit the token in our bank account.
	}

	// can only be called when terminal contains an initialised card (that is temporarily blocked)
	// does not change status of terminal
	// method can throw an exception if the current pin code is not the master pin code
	/*@ requires status == FILLED_INIT;
        requires card.status == Card.TEMP_BLOCKED;
    	ensures status == \old(status);
    	signals_only CardException;
    	signals (CardException) 
       	   status == \old(status) &&
           (\exists int i; 0 <= i && i < card.master_pin.length; pin[i] != card.master_pin[i]); 
    */
	public void unlock() throws CardException {
		card.unlock(pin);
	}
  
	// can only be called when terminal contains a card that is ready for initialisation
	// sets status of terminal to FILLED_INIT
	// method cannot throw an exception
	/*@ requires status == FILLED_READYFORINIT;
	    ensures status == FILLED_INIT;
	    signals (Exception) false;
	 */
	public void initCard() throws CardException {
		card.CardInit(pin,pin);
		//@ set status = FILLED_INIT;
	}
  
	// can only be called when terminal contains an active, initialised card
	// cannot throw an exception
	/*@ requires status == FILLED_INIT;
	    ensures \result == card.amount;
	    signals (Exception) false;
	 */
	public /*@ pure */ int balance(){
		return card.getAmount();
	}
}

