class Customer {

    int ticket;
    int phase = 0;
    static int max = 0;

    //@ static invariant max >= 0;

    // only one customer in crit section
    /*@ static invariant
      @   (\forall Customer c1; \created(c1);
            (\forall Customer c2; \created(c2);
      @      c1.phase == 2 && c2.phase == 2 ==> c1 == c2));
      @*/

    // customer in crit section is minimal
    /*@ static invariant
      @   (\forall Customer c1; \created(c1) && c1.phase==2;
      @      (\forall Customer c2; \created(c2) && c1!=c2 && c2.phase >= 1; 
      @         c2.ticket > c1.ticket));
      @*/

    //@ invariant phase >= 0 && phase <= 2;
    //@ invariant ticket >= 0 && ticket <= max;

    /*@
      @ requires phase == 1 && 
      @   (\forall Customer c; \created(c) && c!=this && c.phase >= 1; 
      @       c.ticket > ticket);
      @ ensures phase == 2;
      @*/
    void enter() {
	phase = 2;
    }

    /*@
      @ requires phase == 2;
      @ ensures phase == 0;
      @ ensures ticket == 0;
      @*/
    void leave() {
	phase = 0;
	ticket = 0;
    }

    /*@
      @ requires phase == 0;
      @ ensures phase == 1;
      @*/
    void request() {
	phase = 1;
	ticket = ++max;
    }
}