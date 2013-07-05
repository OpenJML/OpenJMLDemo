
public interface Student {

    public static final int bachelor = 0;
    public static final int master = 1;

    /*@ pure */ public String getName(); 

    //@ ensures \result == bachelor || \result == master;
    /*@ pure */ public int getStatus();

    //@ ensures \result >= 0;
    /*@ pure */ public int getCredits();

    //@ ensures getName().equals(n);
    public void setName(String n);

    /*@ requires c >= 0;
        ensures getCredits() == \old(getCredits()) + c;
    */
    public void addCredits(int c);

    /*@ requires getCredits() >= 180;
        requires getStatus() == bachelor;
        ensures getCredits() == \old(getCredits());
        ensures getStatus() == master;
    */
    public void changeStatus();

}
