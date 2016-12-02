class Customer {

    int ticket;
    int phase = 0;
    static int max = 0;

    //@ static invariant max >= 0;

    // only one customer in crit section

    /*@  invariant
      @   this.phase == 2 ==> (\forall Customer c2; ;
      @      					c2.phase == 2 ==> this == c2);
      @*/

    // customer in crit section is minimal
    /*@ invariant
      @   this.phase==2 ==>
      @      (\forall Customer c2; c2.phase == 1; 
      @         c2.ticket > this.ticket);
      @*/
    /*@ invariant
      @   this.phase==1 ==>
      @      (\forall Customer c2; c2.phase == 2; 
      @         this.ticket > c2.ticket);
      @*/

    // all customers have a ticket not greater than max
    /*@ static invariant
      @      (\forall Customer c2; c2.phase == 1 || c2.phase == 2; 
      @         c2.ticket <= max);
      @*/

    //@ invariant phase == 0 || phase == 1 || phase == 2;
    //@ invariant ticket >= 0 && ticket <= max;

    /* @
    @ requires phase == 1 && 
    @   (\forall Customer c; \created(c) && c!=this && c.phase >= 1; 
    @       c.ticket > ticket);
    @ ensures phase == 2;
    @*/
    /*@
    @ requires phase == 1 && 
    @   (\forall Customer c;  c!=this && c.phase >= 1; 
    @       c.ticket > ticket);
    @ assignable phase;
    @ ensures phase == 2;
    @*/
    void enter() {
	phase = 2;
    }

    /*@
      @ requires phase == 2;
      @ assignable phase, ticket;
      @ ensures phase == 0;
      @ ensures ticket == 0;
      @*/
    void leave() {
	phase = 0;
	ticket = 0;
    }

    /*@
      @ requires phase == 0;
      @ assignable phase, ticket, max;
      @ ensures phase == 1 && max == \old(max) + 1 && ticket == max;
      @*/
    void request() {
	phase = 1;
	ticket = ++max;
    }
}