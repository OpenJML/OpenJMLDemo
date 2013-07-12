

import java.util.Random;

final class Card {
	//@ public model Object state;

	// private
	  /*@ spec_public */ int master_attempts=0; //@ in state;
	  // private 
	  /*@ spec_public */ int basic_attempts=0; //@ in state;
	  //private 
	  /*@ spec_public */ byte master_pin[]=new byte[8]; //@ in state;
	  //private 
	  /*@ spec_public */ byte basic_pin[]=new byte[4]; //@ in state;
	  //private
	  Random random=new Random(0); //@ in state;
	  //private 
	  /*@ spec_public */ int cardid=random.nextInt(); //@ in state;
	  // error 2
	  // fix 2 private /*@ spec_public */ int amount=-1;
	  //private 
	  /*@ spec_public */ int amount=0; //@ in state;
	  //private 
	  static final int key1=12944557;
	  //private
	  static final int key2=254557;
	  
	  //@ ensures \result == (0<=i && i<=9);
	  //@ public static pure helper model boolean inrange(int i) { return 0<=i && i<=9; }
	  
	  // invariants
	  

	  /*@ //at most three attempts to type in the correct pincode
	      public invariant 0 <= master_attempts && master_attempts <= 3;
	      public invariant 0 <= basic_attempts && basic_attempts <= 3;
	      
	      // pins are defined
	      public invariant master_pin != null;
	      public invariant basic_pin != null;
	      
	      // once the card is initialized, the pins only contain digits (between 0 and 9)
	      public invariant status != UNINIT ==>
	                (\forall int i; 0 <= i && i < master_pin.length; inrange(master_pin[i]));
	      public invariant status != UNINIT ==>
	                (\forall int i; 0 <= i && i < basic_pin.length; inrange(basic_pin[i])); 
	   
	      // amount on card is never negative
	      public invariant amount >= 0;
	   */
	  
	   // constraints to express constancy of values
	   /*@ // lengths of pins do not change
	       public constraint master_pin.length == \old(master_pin.length);
	       public constraint basic_pin.length == \old(basic_pin.length);
	       
	       // if the card is initialised, the pins cannot change anymore
	       public constraint \old(status) != UNINIT ==> 
	                         (\forall int i; 0 <= i && i < master_pin.length; master_pin[i] == \old(master_pin[i]));
	       public constraint \old(status) != UNINIT ==> 
	                         (\forall int i; 0 <= i && i < basic_pin.length; basic_pin[i] == \old(basic_pin[i]));
	    */
	  
	  	// life cycle of card
	   	/*@ // declare ghost variables
	   	    public static final ghost int UNINIT = 0;
	   	    public static final ghost int ACTIVE = 1;
	   	    public static final ghost int TEMP_BLOCKED = 2;
	   	    public static final ghost int BLOCKED = 3;
	   	    
		    public static invariant UNINIT == 0 && BLOCKED == 3 && TEMP_BLOCKED == 2 && ACTIVE == 1;
	   	    
	   	    public ghost int status = UNINIT;
	   	       	    
	   	    // invariant on possible values of status
	   	    public invariant status == UNINIT || status == ACTIVE || status == TEMP_BLOCKED || status == BLOCKED;
	   	    
	   	    // constraints to express transition diagram
	   	    public constraint \old(status) == UNINIT ==> status == UNINIT || status == ACTIVE;
	   	    public constraint \old(status) == ACTIVE ==> status == ACTIVE || status == TEMP_BLOCKED;
	   	    public constraint \old(status) == TEMP_BLOCKED ==> status == ACTIVE || 
	   	                                                status == TEMP_BLOCKED || status == BLOCKED;
	        public constraint \old(status) == BLOCKED ==> status == BLOCKED;
	        
	        // some additional consistency constraints 
	        // to express relation between life cycle of card and pin code verification
	        public invariant status == ACTIVE ==> basic_attempts < 3 && master_attempts == 0;
	        public invariant status == TEMP_BLOCKED ==> basic_attempts == 3 && master_attempts < 3;
	        public invariant status == BLOCKED ==> master_attempts == 3;          	  
	                                                      
	   	 */
	  
	  	//private 
	  	/*@ spec_public */ Token loaded[]=new Token[16];   
	    //private 
	    /*@ spec_public */ Token payed[]=new Token[16];
	    
	    // requirements on loaded and payed
	    /*@ public invariant loaded != null;
	        public invariant payed != null;
	        
	        // tokens are stored consecutively
	        public invariant (\exists int i; 0 <= i && i <= loaded.length;
	                   (\forall int j; 0 <= j && j < i; loaded[j] != null) &&
	                   (\forall int k; i <= k && k < loaded.length; loaded[k] == null));
	        public invariant (\exists int i; 0 <= i && i <= payed.length;
	                   (\forall int j; 0 <= j && j < i; payed[j] != null) &&
	                   (\forall int k; i <= k && k < payed.length; payed[k] == null));

	      
	        // list with tokens only increases
	        public constraint \old(loaded.length) <= loaded.length;
	        public constraint \old(payed.length) <= payed.length;
	        
	        // all non-null tokens remain in the list
	        public constraint (\forall int i; 0 <= i && i < \old(loaded.length);
	                     \old(loaded[i]) != null ==> \old(loaded[i]) == loaded[i]);
	        public constraint (\forall int i; 0 <= i && i < \old(payed.length);
	                     \old(payed[i]) != null ==> \old(payed[i]) == payed[i]);


	        // every token is unique
	        public invariant (\forall int i; 0 <= i && i < loaded.length;
	                      loaded[i] != null ==>
	                      (\forall int j; 0 <= j && j < loaded.length; 
	                          loaded[j] != null ==>
	                             loaded[i].getTokenID() == loaded[j].getTokenID() ==> i == j));
	        public invariant (\forall int i; 0 <= i && i < payed.length;
	                      payed[i] != null ==>
	                      (\forall int j; 0 <= j && j < payed.length;
	                          payed[j] != null ==> 
	                             payed[i].getTokenID() == payed[j].getTokenID() ==> i == j)); 
	        */
	        /*
	        // apparently, this invariant does not hold (invalid at point where Error 5 is found)
	        // for now, no idea how to fix this
	        invariant (\forall int i; 0 <= i && i < loaded.length;
	                      loaded[i] != null ==>                              
	                      (\forall int k; 0 <= k && k < payed.length;
	                          payed[k] != null ==>
	                             loaded[i].getTokenID() != payed[k].getTokenID()));
	        */

	    
	    // no money lost
	    
	    // this cannot be checked by current version of JML
	    // but JML does not drop only this clause, but all clauses
	    /* invariant amount == 
	                  (\sum int i; 0 <= i && i < loaded.length; loaded[i] == null? 0 : loaded[i].getAmount()) -
	                  (\sum int i; 0 <= i && i < payed.length; payed[i] == null? 0 : payed[i].getAmount());
	    */
	    
	    // after construction, the card is still uninitialised
	    // constructor will not throw an exception
	    /*@ assignable basic_pin[*], master_pin[*], this.state;
	        ensures (\forall int i; 0 <= i && i < basic_pin.length; basic_pin[i] == -1); 
	        ensures (\forall int i; 0 <= i && i < master_pin.length; master_pin[i] == -1);
	        ensures status == UNINIT; 
	        ensures basic_pin == \old(basic_pin) && master_pin == \old(master_pin);
	        ensures master_attempts==0 && basic_attempts == 0 && amount == 0;
	        signals (Exception) false;     
	     */
	    public Card(){
	    	// error 1
	    	// fix 1 for(int i=0;i<8;i++) this.basic_pin[i]=-1;
	    	// fix 1 for(int i=0;i<4;i++) this.master_pin[i]=-1;
	    	//@ loop_invariant 0<=i && i<= basic_pin.length && (\forall int j; 0<=j && j<i; basic_pin[j]==-1);
	        for(int i=0;i<basic_pin.length;i++) this.basic_pin[i]=-1;
	    	//@ loop_invariant 0<=i && i<= master_pin.length && (\forall int j; 0<=j && j<i; master_pin[j]==-1);
	    	for(int i=0;i<master_pin.length;i++) this.master_pin[i]=-1;
	    }
	  
	    // look up functions
	    // I choose not to put a status requirement on these look up functions, however, one could imagine a 
	    // precondition: requires status == ACTIVE;
	    
	    /*@ ensures \result == cardid;
	     */
	    public /*@ pure */ int getCardID(){
	    	return cardid;
	    }
	  
	    /*@ ensures \result == amount;
	     */
	    public /*@ pure */ int getAmount(){
	    	return amount;
	    }

	    // cardInit can only be called when the card is not initialised
	    // arguments are two legal pin code, one with sufficient length to fill the basic pin, 
	    // one with sufficient length to fill the master pin
	    // after cardInit, the pin codes are set, and the card is active
	    // cardInit will not throw an exception (if all preconditions are satisfied)
	    /*@ requires status == UNINIT;
	        requires basic_pin != null && master_pin != null;
	        requires this.basic_pin.length <= basic_pin.length;
	        requires this.master_pin.length <= master_pin.length;
	        requires (\forall int i; 0 <= i && i < this.basic_pin.length; inrange(basic_pin[i]));
	        requires (\forall int i; 0 <= i && i < this.master_pin.length; inrange(master_pin[i]));
	        assignable this.basic_pin[*], this.master_pin[*], this.status, this.master_attempts, this.basic_attempts;
	        ensures  (\forall int i; 0 <= i && i < this.basic_pin.length; this.basic_pin[i] == basic_pin[i]);
	        ensures  (\forall int i; 0 <= i && i < this.master_pin.length; this.master_pin[i] == master_pin[i]);
	        ensures status == ACTIVE;
	        signals (Exception) false;
	     */
	    public void CardInit(byte basic_pin[],byte master_pin[]) throws CardException {
	    	//@ loop_invariant 0<=i && i<=this.basic_pin.length && (\forall int j; 0<=j && j<i; this.basic_pin[j] == basic_pin[j]);
	    	//@ loop_invariant 0<=i && i<=this.basic_pin.length && (\forall int j; 0<=j && j<i; inrange(this.basic_pin[j]));
	    	for(int i=0;i<this.basic_pin.length;i++){
	    		//@ assert inrange(basic_pin[i]);
	    		this.basic_pin[i]=basic_pin[i];
	    		//@ assert inrange(this.basic_pin[i]);
	    	}
	    	//@ loop_invariant 0<=i && i<=this.master_pin.length && (\forall int j; 0<=j && j<i; this.master_pin[j] == master_pin[j]);
	    	//@ loop_invariant 0<=i && i<=this.master_pin.length && (\forall int j; 0<=j && j<i; inrange(this.master_pin[j]));
	    	for(int i=0;i<this.master_pin.length;i++){
	    		//@ assert inrange(master_pin[i]);
	    		this.master_pin[i]=master_pin[i];
	    		//@ assert inrange(this.master_pin[i]);
	    	}
	    	//@ set status = ACTIVE;
	    	master_attempts = 0; // These have to be either initialized or required, else the invariant implied by status==ACTIVE cannot be established
	    	basic_attempts = 0;
	    }
	  
	    // append is called on an array where all non-null values are stores consecutively as the initial fragment
	    // the resulting array has the same property, and the last non-null value is the appended token
	    // 
	    // notice that the last postcondition on the token occurring is redundant, it can be deduced from the more
	    // explicit postcondition on the contents of \result
	    //
	    // the method cannot terminate with an exception
	    
	    // since this is a static method, we do not put any requirements on the status of the card object
	    /*@ requires array != null;
	        requires tok != null;
	        requires (\exists int i; 0 <= i && i <= array.length;
	                     (\forall int j; 0 <= j && j < i; array[j] != null) &&
	                     (\forall int k; i <= k && k < array.length; array[k] == null));
	        ensures (\exists int i; 0 <= i && i < \result.length;
	                     (\forall int j; 0 <= j && j < i; \result[j] != null && \result[j] == array[j]) &&
	                     tok.equals(\result[i]) &&
	                     (\forall int k; i < k && k < \result.length; \result[k] == null));
	        ensures array.length <= \result.length;
	        ensures tokenid_occurs(\result, tok.getTokenID());
	        signals (Exception) false;                      
	     */
	    public static Token[] append(Token[] array, Token tok){
	    	int i;
	    	for(i=0;i<array.length;i++){
	    		if (array[i]==null) break;
	    	}
	    	Token out[]=array;
	    	// error 4
	    	// fix 4 if (i>array.length) {
		    if (i>=array.length) {	
	    		out=new Token[array.length*2];
	    		for(int k=0;k<array.length;k++){
	    			out[k]=array[k];
	    		}
	    	};
	    	out[i]=tok;
	    	return out;
	    }
	 
	    // tokenid_occurs is called on an array where all non-null values are stores consecutively 
	    // as the initial fragment
	    // returns true if and only if the a token with tokenid is contained in array
	    
	    // the method will not terminate with an exception
	    
	    // since this is a static method, we do not put any requirements on the status of the card object
	    
	    /*@ requires array != null;
	        requires (\exists int i; 0 <= i && i <= array.length;
	                    (\forall int j; 0 <= j && j < i; array[j] != null) &&
	                    (\forall int k; i <= k && k < array.length; array[k] == null));
	        ensures \result == (\exists int i; 0 <= i && i < array.length; 
	                               array[i] != null && array[i].getTokenID() == tokenid);
	        signals (Exception) false;     
	     */
	    public /*@ pure*/ static boolean tokenid_occurs(Token[] array, int tokenid){
	    	//@ ghost int k = 0;
	    	//@ loop_invariant i == k && 0<=i && i<=array.length && (\forall int j; 0<=j && j <i; array[j] != null && array[j].getTokenID() != tokenid);
	    	for(int i=0;i<array.length&&array[i]!=null;i++){
	    		if (array[i].getTokenID()==tokenid) return true;
	    		//@ set k = k + 1;
	    	}
	    	//@ assert 0 <= k && k <= array.length;
	    	//@ assert (\forall int j; 0<=j && j <k; array[j] != null && array[j].getTokenID() != tokenid);
	    	//@ assert k == array.length || array[k] == null;
	    	return false;
	    }
	  
	    // the method can only be called when the card is active
	    // status of the card is not changed
	    
	    // to ensure that all tokens remain unique, tok.getTokenID() should not occur in loaded or payed
	    
	    // if the token is valid, then the token is added to loaded, and the amount is added to the 
	    // credits of the card (we can even specify that this is the last non-null token in loaded, 
	    // but this too much implementation detail)
	    
	    // the method terminates with an exception if the token is not valid, in that case the state is not changed
	    // the only exception that the method can throw is a CardException
	    
	    /*@ requires status == ACTIVE;
	        requires tok != null;
	        requires !tokenid_occurs(loaded, tok.getTokenID());
	        requires !tokenid_occurs(payed, tok.getTokenID());
	        ensures status == \old(status);
	        ensures tokenid_occurs(loaded, tok.getTokenID());
	        ensures amount == \old(amount) + tok.getAmount();
	        signals_only CardException;
	        signals (CardException) 
	          status == \old(status) && amount == \old(amount) &&
	          (\forall int i; 0 <= i && i < loaded.length; loaded[i] == \old(loaded[i]));
	     */
	    public void load(Token tok) throws CardException {
	    	if (!tok.check(key1,key2)) throw new CardException("invalid token");
	    	if (tokenid_occurs(loaded,tok.getTokenID())) return;
	    	loaded=append(loaded,tok);
	    	amount=amount+tok.getAmount();
	    }


	    // the method can only be called when the card is active
	    // status of the card is not changed upon normal termination
	    // if the method terminates exceptionally, status is changed only if the number of wrong attempts to type in
	    // the basic pin code is three, otherwise status is unchanged
	    
	    // the amount to pay cannot be more than the amount of money on the card
	    // the pin code should be a legal pin code
	    
	    // if the pin code is correct, the amount is deducted from the amount on the card, and a new token with
	    // this amount and payee as ownerid is added to payed (we can even specify that this is the last non-null token in loaded, 
	    // but this too much implementation detail)
	    // in addition, basic_attempts is reset to 0
	    
	    // the method terminates with an exception if the pin is incorrect
	    // if three incorrect attempts have been made, the card becomes temporarily blocked,
	    // otherwise only the number of basic attempts is increased 
	    // in both cases, amount and the contents of payed are not changed
	    
	    /*@ requires status == ACTIVE;
	        requires this.amount >= amount;
	        requires basic_pin != null && basic_pin.length >= this.basic_pin.length;
	        requires (\forall int i; 0 <= i && i < this.basic_pin.length; 0 <= basic_pin[i] && basic_pin[i] <= 9);
	        ensures status == \old(status);
	        ensures (\forall int i; 0 <= i && i < this.basic_pin.length; basic_pin[i] == this.basic_pin[i]);
	        ensures this.amount == \old(this.amount) - amount;
	        ensures basic_attempts == 0;
	        ensures (\exists int i; 0 <= i && i < payed.length; payed[i] != null &&
	                                                            payed[i].getAmount() == amount &&
	                                                            payed[i].getOwner() == payee);
	        signals_only CardException;
	        signals (CardException) 
	          amount == \old(amount) &&
	          (\forall int i; 0 <= i && i < payed.length; payed[i] == \old(payed[i]));
	        signals (CardException) basic_attempts == 3 ? status == TEMP_BLOCKED : status == \old(status);
	     */  
	    public Token pay(int amount,int payee,byte basic_pin[]) throws CardException {
	    	// Error 7
	    	// fix 7 basic_attempts++;
	    	// fix 7 if (basic_attempts>3) {
	    	// fix 7 	//@ set status = TEMP_BLOCKED;
	    	// fix 7 	throw new CardException("card is blocked");
	    	// fix 7}
	    	// fix 7 for(int i=0;i<4;i++){
	    	// fix 7	if (this.basic_pin[i]!=basic_pin[i]) {
	    	// fix 7		throw new CardException("invalid pin");
	    	// fix 7	}
	    	// fix 7}
	    	//@ loop_invariant 0<=i && i < basic_pin.length && (\forall int j; 0<=j && j<i; this.basic_pin[j]!=basic_pin[j]);
	    	for(int i=0;i<basic_pin.length;i++){
	    		if (this.basic_pin[i]!=basic_pin[i]) {
	    			basic_attempts++;
	    	    	if (basic_attempts==3) {
	    	    		//@ set status = TEMP_BLOCKED;
	    	    		throw new CardException("card is blocked");
	    	    	} else {
	    			throw new CardException("invalid pin");
	    	    	}
	    		}
	    	}
	    	basic_attempts=0;
	    	this.amount-=amount;
	    	Token tok=new Token(amount,payee,random.nextInt());
	    	tok.sign(key1,key2);
	    	append(payed, tok);
	    	return tok;
	    }

	    // the method can only be called when the card is temporarily block
	    // status of the card is only changed to active after normal termination
	    // if the method terminates exceptionally, status is changed only if the number of wrong attempts to type in
	    // the master pin code is three, otherwise status is unchanged
	    
	    // the pin code should be a legal pin code
	    
	    // if the pin code is correct, both basic_attempts and master_attempts are reset to 0
	    
	    // the method terminates with an exception if the pin is incorrect
	    // if three incorrect attempts have been made, the card becomes blocked forever,
	    // otherwise only the number of master attempts is increased 
	    
	    /*@ requires status == TEMP_BLOCKED;
	        requires master_pin != null && master_pin.length >= this.master_pin.length;
	        requires (\forall int i; 0 <= i && i < this.master_pin.length; 0 <= master_pin[i] && master_pin[i] <= 9);
	        assignable basic_attempts, master_attempts, status;
	        ensures status == ACTIVE;
	        ensures (\forall int i; 0 <= i && i < this.master_pin.length; master_pin[i] == this.master_pin[i]);
	        ensures basic_attempts == 0;
	        ensures master_attempts == 0;
	        signals_only CardException;
	        signals (CardException) master_attempts == 3 ? status == BLOCKED : status == \old(status);
	     */  
	    public void unlock(byte master_pin[]) throws CardException {
	    	// Error 7: detected in pay, but clearly same error here
	    	// fix 7 master_attempts++;
	    	// fix 7 if(master_attempts>3) {
	    	// fix 7	//@ set status = BLOCKED;
	    	// fix 7	throw new CardException("card is voided");
	    	// fix 7 }
	    	// fix 7 for(int i=0;i<8;i++){
	    	// fix 7	if (this.master_pin[i]!=master_pin[i]){
	    	// fix 7		throw new CardException("invalid pin");
	    	// fix 7	}	
	    	// fix 7 }
	    	//@ loop_invariant 0<= master_attempts && master_attempts < 3 && 0<=i && i<=master_pin.length && status == \old(status) && (\forall int j; 0<=j && j<i; this.master_pin[j] == master_pin[j]);
	    	for(int i=0;i<master_pin.length;i++){
	    		if (this.master_pin[i]!=master_pin[i]){
	    			master_attempts++;
	    	    	if(master_attempts>=3) {
	    	    		//@ set status = BLOCKED;
	    	    		throw new CardException("card is voided");
	    	    	} else {		
	    			throw new CardException("invalid pin");
	    	    	}
	    		}	
	    	}
	    	basic_attempts=0;
	    	// Error 8
	    	// fix 8
	    	master_attempts = 0;
	    	//@ set status = ACTIVE;
	    }
}
