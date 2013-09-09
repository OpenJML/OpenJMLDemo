
class CStudent implements Student {

	/*@ spec_public */ private String name;
    /*@ spec_public */ private int credits;
    /*@ spec_public */ private int status;
    /*@ spec_public */ private boolean active;

    /*@ requires c >= 0;
        ensures getCredits() == c;
        ensures getStatus() == bachelor;
        ensures getName() == n;
    */
    CStudent (int c, String n) {
        credits = c;
        name = n;
        status = bachelor;
    }

    public String getName() {
        return name;
    }

    public int getStatus() {
        return status;
    }

    public int getCredits() {
        return credits;
    }

    public void setName(String n) {
        name = n;
    }

    public void becomeActive() {
        active = true;
    }

    public void addCredits(int c) {
        credits = credits + c;
    }

    public void changeStatus() {
        status = master;
    }

    /*@ requires 0 <= bonus && bonus <= 5 && active;
        {|
          requires getStatus() == bachelor;
          ensures getCredits() ==
            (\old(getCredits()) + bonus > 180 ? 
              180 : \old(getCredits()) + bonus);
          also
          requires getStatus() == master;
          ensures getCredits() == \old(getCredits() + bonus);
        |}
        // also: other specification for students that are not active
    */
    public void activityBonus(int bonus) {
        if (active) { addCredits(bonus); }
    }
}
