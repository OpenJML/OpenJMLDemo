/**
 * A piece of marked ground. 
 */
public class MarkedGround extends Ground
{

  //@ ensures position.equals(p);
  MarkedGround ( /*@ non_null @*/ Position p) {
    super (p);
  }

  //@ also
  //@ ensures \result;
  /*@ pure @*/ public boolean isMarked () {
    return true;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString () {
    return "groundX(" + position.x + "," + position.y + ")";
  }
}
