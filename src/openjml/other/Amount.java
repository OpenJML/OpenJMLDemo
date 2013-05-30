package sv_esc;


/* solution */

public class Amount{

 private int cents;
 //@ private invariant -100 < this.cents && this.cents < 100;

 private int euros;
 //@ private invariant !(this.euros < 0 && this.cents > 0); 
 //@ private invariant !(this.euros > 0 && this.cents < 0);

 // There are other ways of writing this, eg
 //  invariant cents < 0 ==> euros <= 0;
 //  invariant cents > 0 ==> euros >= 0;

 //@ requires -100 < cents && cents < 100;
 //@ requires !(euros < 0 && cents > 0); 
 //@ requires !(euros > 0 && cents < 0);
 public Amount(int euros, int cents){
   this.euros = euros;
   this.cents = cents;
 }

 //@ ensures \result != null;
 public /*@ non_null @*/ Amount negate(){
   return new Amount(-euros,-cents); // error fixed
   // return new Amount(-cents,-euros); // error in code
 }

 // @ requires a != null;
 public /*@ non_null @*/ Amount decrease(/*@ non_null @*/ Amount a){
   Amount t = a.negate();
   return this.increase(t);
 }

 //@ requires a != null;
 public /*@ non_null @*/ Amount increase(/*@ non_null @*/ Amount a){
   int new_euros = euros + a.euros;
   int new_cents = cents + a.cents; 
   if (new_cents < -99) {  // error fixed
   // if (new_cents < -100) {  // error in code
      new_cents = new_cents + 100;
      new_euros = new_euros - 1;
   } 
   if (new_cents > 99) {  // error fixed
   // if (new_cents > 100) {  // error in code
      new_cents = new_cents - 100;
      new_euros = new_euros - 1;
   } 
   if (new_cents < 0 && new_euros > 0) { 
       new_cents = new_cents + 100; 
       new_euros = new_euros - 1;
   } 
   if (new_cents > 0 && new_euros < 0) {
   // if (new_cents >= 0 && new_euros <= 0) { // error in code
       new_cents = new_cents - 100; 
       new_euros = new_euros + 1;
   }
   return new Amount(new_euros,new_cents);
 }

 public boolean equal(/*@ non_null @*/ Amount a) {
   if (a==null) return false;
   else return (euros == a.euros && cents == a.cents);
 }


}
