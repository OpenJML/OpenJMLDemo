
public class BoardItem {

    public boolean ground; // true if the square is valid playing area (not a wall)
    public boolean marked; // true if the square is a target location
    public boolean crate; // true if the square contains a crate
    
    //@ model public boolean isOpen; // true if square is part of playable area, but does not have a crate
    //@ represents isOpen = ground && !crate;
    
    //@ ensures !ground && !crate && !marked;
    //@ pure
    public BoardItem() {
        ground = false;
        marked = false;
        crate = false;
    }
}
