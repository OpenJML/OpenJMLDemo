/**
 * A wall piece on the board, untouchable. 
 */
final class Wall implements BoardItem
{

  /** Position of the wall is fixed, hence the field is final. */
  /*@ spec_public @*/ final /*@ non_null @*/ Position position;

  //@ ensures position.equals(p);
  Wall ( /*@ non_null @*/ Position p) {
    position = p;
  }

  //@ also
  //@ ensures !\result;
  /*@ pure helper @*/ public boolean isCanStepOn () {
    return false;
  }

  //@ also
  //@ ensures !\result;
  /*@ pure helper @*/ public boolean isMovable () {
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

  //@ also
  //@ ensures !\result;
  /*@ pure helper @*/ public boolean isMarked () {
    return false;
  }

  //@ skipesc
  public /*@ pure non_null @*/ String toString () {
    return "wall(" + position.x + "," + position.y + ")";
  }

}
