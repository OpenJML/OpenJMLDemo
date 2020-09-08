/**
 * Represents the board of the game. The board is by default always square.
 */
final class Board {

  /*@ spec_public @*/ int xSize;
  //@ public invariant xSize > 0; 

  /*@ spec_public @*/ int ySize;
  //@ public invariant ySize > 0; 

  /*@ spec_public non_null @*/ BoardItem[][] items;

  /** The board has the right size */

  //@ public invariant items.length == xSize;
  /*@ public invariant (\forall int x;
    @   x >= 0 && x < xSize;
    @      items[x] != null && items[x].length == ySize && \elemtype(\typeof(items[x])) == \type(BoardItem));
    @*/

  /*@ public invariant (\forall int x;
    @    x>=0 && x < xSize && items[x] != null;
    @       (\forall int y; y>=0 && y < ySize; items[x][y] != null));
    @*/


  /** The items that are placed on the board have consistent position information */
  // FIXME = for now, omitting invariants with method calls instide quantifiers
  /* @ public invariant (\forall int x;
    @    x>=0 && x < xSize && items[x] != null;
    @       (\forall int y; y>=0 && y < ySize; 
    @            items[x][y]._position.x == x && items[x][y]._position.y == y));
    @*/


  /** Creates an empty board.
    */
  //@ requires xSize > 0;
  //@ requires ySize > 0;
  //@ ensures this.xSize == xSize;
  //@ ensures this.ySize == ySize;
  Board (int xSize, int ySize) {
    this.xSize = xSize;
    this.ySize = ySize;
    items = new BoardItem[xSize][ySize];
    //+ESC@ assume (\forall int xx; 0 <= xx && xx < xSize; items[xx] != null && items[xx].length == ySize && \fresh(items[xx]) && \elemtype(\typeof(items[xx])) == \type(BoardItem));
    a:{}
    
    //@ loop_invariant 0 <= x && x <= xSize;
    //@ loop_invariant (\forall int xx; 0<=xx && xx<x; (\forall int yy; 0<=yy && yy <ySize; items[xx][yy] != null));
    for (int x = 0; x < xSize; x++) {
      //@ loop_invariant 0 <= y && y <= ySize;
      //@ loop_invariant (\forall int yy; 0<=yy && yy <y; items[x][yy] != null);
      for (int y = 0; y < ySize; y++) {
        //+ESC@ assume \fresh(items[x]);
        // +ESC@ assume items[x] == \old(items,a)[x]; // FIXME - this should be sufficient but is not
        items[x][y] = new Ground (new Position (x, y));
      }
    }
  }

  /** Used to build some meaningful game board. */
  //@ requires item.position().x < xSize;
  //@ requires item.position().y < ySize;
  //@ assignable items[item.position().x][item.position().y];
  void putItemOnBoard ( /*@ non_null @*/ BoardItem item) {
    items[item.position().x][item.position().y] = item;
  }

}
