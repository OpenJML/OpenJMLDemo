/**
 * A piece of unmarked ground. 
 */
class Ground implements BoardItem
{

  /*@ spec_public @*/ final /*@ non_null @*/ Position position;

  //@ ensures position == p;
  //@ pure
  Ground ( /*@ non_null @*/ Position p) {
    position = p;
  }

  //@ also 
  //@ ensures \result;
  /*@ pure helper @*/ public boolean isCanStepOn () {
    return true;
  }

  //@ also 
  //@ ensures !\result;
  /*@ pure helper @*/ public boolean isMovable () {
    return false;
  }

  //@ also 
  //@ ensures !(this instanceof MarkedGround) ==> !\result;
  /*@ pure helper @*/ public boolean isMarked () {
    return false;
  }

  //@ also 
  //@ ensures \result == position;
  /*@ pure @*/ public /*@ non_null @*/ Position position () {
    return position;
  }

  public void setPosition ( /*@ non_null @*/ Position newPosition)
      throws IllegalStateException {
    throw new IllegalStateException ();
  }

  //@ skipesc
  public /*@ non_null @*/ String toString () {
    return "ground(" + position.x + "," + position.y + ")";
  }

}
