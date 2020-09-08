/**
 * A crate on the board that can be moved, and is standing on a marked position. 
 */
public final class MarkedCrate extends Crate
{

  MarkedCrate (Position p) {
    super (p);
  }

  //@ also 
  //@ ensures \result;
  /*@ pure @*/ public boolean isMarked () {
    return true;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString () {
    return "crateX(" + position.x + "," + position.y + ")";
  }

}
