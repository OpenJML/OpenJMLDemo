
class ExecuteCStudent2 {

    public static void main (String [] args) {
        CStudent s = new CStudent(0, "Marieke");
        s.becomeActive();
        s.addCredits(178);
        s.activityBonus(5);
        System.out.println(s.getCredits());
        System.out.println(s.getStatus());
    }
}