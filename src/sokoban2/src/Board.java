/**
 * Represents the board of the game. The board is by default always square.
 */
final class Board {

  /*@ spec_public @*/ int xSize;
  //@ public invariant xSize > 0; 

  /*@ spec_public @*/ int ySize;
  //@ public invariant ySize > 0; 

  /*@  non_null @*/ public boolean[][] ground; // true if the square is valid playing area (not a wall)
  /*@  non_null @*/ public boolean[][] marked; // true if the square is a target location
  /*@  non_null @*/ public boolean[][] crate; // true if the square contains a crate

  /** The board has the right size */

  //@ public invariant ground.length == xSize;
  //@ public invariant marked.length == xSize;
  //@ public invariant crate.length == xSize;
  //@ public invariant ground != crate && ground != marked && marked != crate;
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize;
  @      ground[x] != null && ground[x].length == ySize);
  @*/
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize;
  @      marked[x] != null && marked[x].length == ySize);
  @*/
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize;
  @      crate[x] != null && crate[x].length == ySize);
  @*/
  // All marked locations are in the valid palying area
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize; (\forall int y; y>=0 && y < ySize;
  @      marked[x][y] ==> ground[x][y]));
  @*/
  // All crates are in the valid playing area
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize; (\forall int y; y>=0 && y < ySize;
  @      crate[x][y] ==> ground[x][y]));
  @*/

  /** Creates an empty board.
    */
  //@ requires xSize > 0;
  //@ requires ySize > 0;
  //@ ensures this.xSize == xSize;
  //@ ensures this.ySize == ySize;
  //@ pure
  //@ skipesc // TODO: Problems still with initializing multi-dimensional arrays
  Board (int xSize, int ySize) {
    this.xSize = xSize;
    this.ySize = ySize;
    ground = new boolean[xSize][ySize];
    marked = new boolean[xSize][ySize];
    crate = new boolean[xSize][ySize];
    //@ assume ground.length == xSize && (\forall int x; 0 <=x && x <xSize; ground[x] != null && ground[x].length == ySize);
    //@ assume marked.length == xSize && (\forall int x; 0 <=x && x <xSize; marked[x] != null && marked[x].length == ySize);
    //@ assume crate.length == xSize && (\forall int x; 0 <=x && x <xSize; crate[x] != null && crate[x].length == ySize);
    //@ loop_invariant 0 <= x && x <= xSize;
    //@ loop_invariant (\forall int ix; 0 <= ix && ix < x; (\forall int iy; 0 <= iy && iy < ySize; (crate[ix][iy] ==> ground[ix][iy]) && (marked[ix][iy] ==> ground[ix][iy])));
    //@ decreases xSize - x;
    for (int x = 0; x < xSize; x++) {
        //@ loop_invariant 0 <= y && y <= ySize;
        //@ loop_invariant (\forall int iy; 0 <= iy && iy < y; (crate[x][iy] ==> ground[x][iy]) && (marked[x][iy] ==> ground[x][iy]));
        //@ decreases ySize - y;
        for (int y = 0; y < ySize; y++) {
            //+ESC@ assume \fresh(ground[x]) && \fresh(marked[x]) && \fresh(crate[x]);
            ground[x][y] = false;
            marked[x][y] = false;
            crate[x][y] = false;
            //@ assert (crate[x][y] ==> ground[x][y]) && (marked[x][y] ==> ground[x][y]);
            //@ assert (\forall int iy; 0 <= iy && iy <= y; (crate[x][iy] ==> ground[x][iy]) && (marked[x][iy] ==> ground[x][iy]));
        }
        //@ assert (\forall int ix; 0 <= ix && ix <= x; (\forall int iy; 0 <= iy && iy < ySize; (crate[ix][iy] ==> ground[ix][iy]) && (marked[ix][iy] ==> ground[ix][iy])));
    }
    //@ assert (\forall int ix; 0 <= ix && ix < xSize; (\forall int iy; 0 <= iy && iy < ySize; (crate[ix][iy] ==> ground[ix][iy]) && (marked[ix][iy] ==> ground[ix][iy])));
  }
  
  //@ ensures \result == ( 0 <= p.x && p.x < xSize && 0 <= p.y && p.y < ySize);
  //@ pure helper
  public boolean onBoard(Position p) {
      return 0 <= p.x && p.x < xSize && 0 <= p.y && p.y < ySize;
  }

  // Note: Can't always make a Position from x and y, because Position requires
  // x and y to be non-negative
  //@ ensures \result == ( 0 <= x && x < xSize && 0 <= y && y < ySize);
  //@ pure helper
  public boolean onBoard(int x, int y) {
      return 0 <= x && x < xSize && 0 <= y && y < ySize;
  }

//  /** Used to build some meaningful game board. */
//  //@ requires item.position().x < xSize;
//  //@ requires item.position().y < ySize;
//  void putItemOnBoard ( /*@ non_null @*/ BoardItem item) {
//    items[item.position().x][item.position().y] = item;
//  }

}
