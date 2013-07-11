

class Token {
	//private 
	/*@ spec_public */ int amount;  // the value of the token.
	//@ public invariant amount >= 0;
	
	//private 
	int ownerid; // the unique id of recipient of the token.
	//private 
	int tokenid; // a unique id meant to avoid accepting a token more than once.
	
	//private 
	int sig;     // cryptographic signature.
	//private 
	/*@ spec_public */ boolean signed;
	
	// life cycle of token
	// it has to be signed, before it can be checked
	// once it is signed, it remains signed for ever
	
	/*@ public static final ghost int UNINIT = 0;
	    public static final ghost int SIGNED = 1;
	    
	    public ghost int status = UNINIT;
	
	    public invariant status == UNINIT || status == SIGNED;
	    
	    public constraint \old(status) == UNINIT ==> status == UNINIT || status == SIGNED;
	    public constraint \old(status) == SIGNED ==> status == SIGNED;
	
	    // status is signed if and only if signed flag is set
	    public invariant status == SIGNED <==> signed;
	 */
  
	//@ ensures \result == amount;
	public /*@ pure */ int getAmount(){ return amount; }
	
	public /*@ pure */ int getOwner(){ return ownerid; }
	
	public /*@ pure */ int getTokenID(){ return tokenid; }
	
	//@ requires amount >= 0;
	//@ ensures status == UNINIT;
	//@ signals (Exception) false;
	public Token(int amount,int ownerid,int tokenid){
		this.amount=amount;
		this.ownerid=ownerid;
		this.tokenid=tokenid;
		this.signed=false;
		//@ set status = UNINIT;
	}
  
	// change status from UNINIT to signed
	
	// after this method, calling check with the same arguments should return true
	
	//@ requires status == UNINIT;
	//@ requires key2 != 0;
	//@ ensures status == SIGNED;
	//@ ensures check(key1, key2);
	//@ signals (Exception) false;
	public void sign(int key1,int key2){
		signed=true;
		// error 3: mismatch between sign and check
		// fix 3 sig=((amount*251%2549)*key1)%key2;
		// fix 3 sig+=((ownerid*251%2549)*key1)%key2;
		// fix 3 sig+=((tokenid*251%2549)*key1)%key2;
		sig=amount*251%2549;
		sig+=ownerid*251%2549;
		sig+=tokenid*251%2549;
		sig=(sig*key1)%key2;
		//@ set status = SIGNED;
	}

	//@ public normal_behavior  // NOTE: pure methods must have no exceptional possibilities
	//@ requires status == SIGNED;
	//@ requires key2 != 0;
	// NOTE - need a condition on \result to be able to use this method in sign's specifications
	//@ ensures \result == (status == SIGNED) && (* sig is correctly set *); 
	//  @ ensures status == \old(status); // NOTE: redundant -  is pure so this has to hold
	public /*@ pure */ boolean check(int key1,int key2){
		if (!signed) return false;
		int sig=amount*251%2549;
		sig+=ownerid*251%2549;
		sig+=tokenid*251%2549;
		sig=(sig*key1)%key2;
		return this.sig==sig;
	} 
}
