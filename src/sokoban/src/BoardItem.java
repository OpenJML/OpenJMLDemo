/**
 * Represents an item on the board that occupies one cell. Can
 * be either a piece of the wall (unmovable, cannot be stepped on),
 * a crate (movable, cannot be stepped on), ground (unmovable, can be stepped on).
 * Additionally each crate or ground can be marked. 
 */
public interface BoardItem
{

    //@ model instance public boolean _isMovable; public represents _isMovable = isMovable();
    //@ model instance public boolean _isCanStepOn; public represents _isCanStepOn = isCanStepOn();
    //@ model instance public boolean _isMarked; public represents _isMarked = isMarked(); 
    //@ model instance public Position _position; public represents _position = position();
    
    //@ ensures \result == _isMovable;
  /*@ pure helper @*/ boolean isMovable ();
  //@ ensures \result == _isCanStepOn;
  /*@ pure helper @*/ boolean isCanStepOn ();
  //@ ensures \result == _isMarked;
  /*@ pure helper @*/ boolean isMarked ();

  /** We cannot move ground  */
  //@ invariant isCanStepOn() ==> !isMovable();

  /** Something that can be moved cannot be stepped on */
  //@ invariant isMovable() ==> !isCanStepOn();

  /** Only ground and crates can be marked */
  //@ invariant !isMovable() && !isCanStepOn() ==> !isMarked();

  //@ ensures \result == _position;
  /*@ pure helper non_null @*/ Position position ();

  /**
    * Only movable items can change their position. Moreover,
    * the position can be only changed by one increment in only
    * one direction.
    */

  /*@ public normal_behavior
    @   requires isMovable();
    @   requires position().isValidNextPosition(newPosition); 
    @   ensures position() == newPosition;
    @   assignable \everything;
    @ also
    @ public exceptional_behavior
    @   requires !isMovable() || !position().isValidNextPosition(newPosition);
    @   signals (IllegalStateException) position() == \old(position());
    @   assignable \nothing;
    @*/
  void setPosition ( /*@ non_null @*/ Position newPosition)
      throws IllegalStateException;

}
