/**
 * Stores coordinates of the position on the board.
 */
final class Position
{

  /*@ spec_public @*/ final int x;
  //@ public invariant x >= 0;

  /*@ spec_public @*/ final int y;
  //@ public invariant y >= 0;

  //@ requires x >= 0 && y >= 0;
  //@ ensures this.x == x && this.y == y;
  //@ pure
  Position (int x, int y) {
    this.x = x;
    this.y = y;
  }

  //@ also
  //@ requires o != null && (o instanceof Position);
  //@ ensures \result <==> ((Position)o).x == x && ((Position)o).y == y; 
  /*@ pure @*/ public boolean equals ( /*@ nullable @*/ Object o) {
    if (o instanceof Position) {
      Position q = (Position) o;
      return x == q.x && y == q.y;
    }
    return false;
  }

  /*@ ensures \result <==> 
    @    (newPosition.x == x && (newPosition.y == y - 1 || newPosition.y == y + 1))
    @ || (newPosition.y == y && (newPosition.x == x - 1 || newPosition.x == x + 1));
    @*/
  /*@ spec_public pure @*/ boolean isValidNextPosition (
	       /*@ non_null @*/ Position newPosition) {
	    if (newPosition.x == x) {
	      return newPosition.y == y + 1 || newPosition.y == y - 1;
	    } else if (newPosition.y == y) {
	      return newPosition.x == x + 1 || newPosition.x == x - 1;
	    }
	    return false;
	  }

  /*@ spec_public pure @*/ boolean isValidNextPositionMultiStep (
	       /*@ non_null @*/ Position newPosition) {
	    return (newPosition.x == x) || (newPosition.y == y);
	  }

  //@ skipesc
  public /*@ pure non_null @*/ String toString () {
    return "position(" + this.x + "," + this.y + ")";
  }

}
