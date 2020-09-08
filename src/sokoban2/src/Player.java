/**
 * Represents a player. Technically, a player could be a board item, but we keep 
 * her/him separate. 
 */
final class Player
{

	  /*@ non_null @*/ public Position position;

  //@ ensures this.position == position;
  //@ pure
  Player (Position position) {
	    this.position = position;
  }


  /*@ public normal_behavior
    @   requires position.isValidNextPosition(newPosition); 
    @   assignable position;
    @   ensures position == newPosition;
    @*/
  public void setPosition (Position newPosition) {
	    this.position = newPosition;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString () {
    return "player(" + position.x + "," + position.y + ")";
  }

}
