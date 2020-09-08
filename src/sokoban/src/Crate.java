/**
 * A crate on the board that can be moved, that is not standing on a marked position. 
 */
public class Crate implements BoardItem
{

  /*@ spec_public non_null @*/ Position position;

  //@ ensures position.equals(p);
  Crate ( /*@ non_null @*/ Position p) {
    position = p;
  }
  
  //@ public represents _isCanStepOn = false;

  //@ also 
  //@ ensures !\result;
  /*@ pure helper @*/ public boolean isCanStepOn () {
    return false;
  }

  //@ also 
  //@ ensures \result;
  /*@ pure helper @*/ public boolean isMovable () {
    return true;
  }

  //@ also 
  //@ ensures \result == position;
  /*@ pure @*/ public /*@ non_null @*/ Position position () {
    return position;
  }

  public void setPosition ( /*@ non_null @*/ Position newPosition)
      throws IllegalStateException {
    if (position.isValidNextPosition (newPosition)) {
      position = newPosition;
    } else {
      throw new IllegalStateException ();
    }
  }

  //@ also 
  //@ ensures !(this instanceof MarkedCrate) ==> !\result;
  /*@ pure helper @*/ public boolean isMarked () {
    return false;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString () {
    return "crate(" + position.x + "," + position.y + ")";
  }

}
