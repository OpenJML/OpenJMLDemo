/**
 * Represents a player. Technically, a player could be a board item, but we keep 
 * her/him separate. 
 */
final class Player
{

  /*@ spec_public non_null @*/ Position position;

  //@ ensures position == p;
  Player ( /*@ non_null @*/ Position p) {
    position = p;
  }

  //@ ensures \result == position;
  public /*@ pure non_null helper @*/ Position position () {
    return position;
  }

  /*@ public normal_behavior
    @   requires position().isValidNextPosition(newPosition); 
    @   ensures position() == newPosition;
    @   assignable \everything;
    @*/
  public void setPosition ( /*@ non_null @*/ Position newPosition) {
      position = newPosition;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString () {
    return "player(" + position.x + "," + position.y + ")";
  }

}
