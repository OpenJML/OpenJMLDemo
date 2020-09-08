/**
 * Represents the board of the game. The board is by default always square.
 */
final class Board {

  /*@ spec_public @*/ int xSize;
  //@ public invariant xSize > 0; 

  /*@ spec_public @*/ int ySize;
  //@ public invariant ySize > 0; 

  /*@  non_null @*/ public BoardItem[][] items;

  /** The board has the right size */

  //@ public invariant items.length == xSize;
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize;
  @      items[x] != null && items[x].length == ySize);
  @*/
  // All marked locations are in the valid palying area
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize; (\forall int y; y>=0 && y < ySize;
  @      items[x][y].marked ==> items[x][y].ground));
  @*/
  // All crates are in the valid playing area
  /*@ public invariant (\forall int x;
  @   x >= 0 && x < xSize; (\forall int y; y>=0 && y < ySize;
  @      items[x][y].crate ==> items[x][y].ground));
  @*/
  // TODO: IS it assured that each BoardItem is distinct
  // TODO: Initial board is all wall

  //+ESC@ public pure helper model static int uniquex(BoardItem[] a);
  //+ESC@ public invariant (\forall int x; 0<=x && x < xSize; uniquex(items[x]) == x);
  //+ESC@ public pure helper model static int uniquexx(BoardItem a);
  //+ESC@ public pure helper model static int uniquexy(BoardItem a);
  //+ESC@ public invariant (\forall int x; 0<=x && x < xSize; (\forall int y; 0<=y && y<ySize; uniquexx(items[x][y]) == x));
  //+ESC@ public invariant (\forall int x; 0<=x && x < xSize; (\forall int y; 0<=y && y<ySize; uniquexy(items[x][y]) == y));
  
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
    items = new BoardItem[xSize][ySize];
    //@ assume items.length == xSize && (\forall int x; 0 <=x && x <xSize; items[x] != null && items[x].length == ySize);
    //@ loop_invariant 0 <= x && x <= xSize;
    //@ loop_invariant (\forall int ix; 0 <= ix && ix < x; (\forall int iy; 0 <= iy && iy < ySize; (items[ix][iy].crate ==> items[ix][iy].ground) && (items[ix][iy].marked ==> items[ix][iy].ground)));
    //@ decreases xSize - x;
    for (int x = 0; x < xSize; x++) {
        //@ loop_invariant 0 <= y && y <= ySize;
        //@ loop_invariant (\forall int iy; 0 <= iy && iy < y; (items[x][iy].crate ==> items[x][iy].ground) && (items[x][iy].marked ==> items[x][iy].ground));
        //@ decreases ySize - y;
        for (int y = 0; y < ySize; y++) {
            //+ESC@ assume \fresh(items[x]);
            items[x][y] = new BoardItem();
        }
    }
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
