/**
 * The game of Sokoban is played on a (for simplicity) square board. Each
 * cell of the board is occupied by either:
 *   
 *   - a wall, which is impenetrable
 *   - a ground that can be marked. Marked ground squares have to be covered with
 *     crates to win the game
 *   - a box/crate that can be moved one cell in a horizontal or vertical direction,
 *     provided there is no obstruction behind the crate
 *   - a player itself, that is initially placed on an unoccupied spot and
 *     can move horizontally or vertically keeping in mind the game rules.
 * 
 * The game is won when the player rearranges the board such that all marked ground
 * squares are covered by crates.
 */
final class Game {

  /*@ spec_public non_null @*/ Board board;
  /*@ spec_public non_null @*/ Player player;

  /** Some consistency properties:
    *   - a player has to be within the bounds of the board
    *   - a player can only stand on an "can stand on" board square 
    */

  //@ public invariant player.position().x < board.xSize && player.position().y < board.ySize;
  //@ public invariant board.items[player.position().x][player.position().y].isCanStepOn();


  //@ public model boolean gameStuck;
  /*@ public represents gameStuck = (\forall int x; x >= 0 && x < board.xSize; (\forall int y; y >= 0 && y < board.ySize;
     @    board.items[x][y]._isMovable ==>
     @      (
     @       ( x == 0 || !board.items[x-1][y]._isCanStepOn || x == board.xSize - 1 || !board.items[x+1][y]._isCanStepOn )
     @      &&
     @       ( y == 0 || !board.items[x][y-1]._isCanStepOn || y == board.ySize - 1 || !board.items[x][y+1]._isCanStepOn )
     @      )
     @ ));
     @*/
  //@ public invariant !gameWon ==> !gameStuck;

  //@ public model boolean gameWon;
  /*@ public represents gameWon =
    @      (\forall int x; x>=0 && x < board.xSize;
    @          (\forall int y; y>=0 && y < board.ySize;
    @               board.items[x][y]._isMarked ==> (board.items[x][y] instanceof Crate))); 
    @*/

  /** Create new game */
  //@ requires player.position().x < board.xSize && player.position().y < board.ySize;
  //@ requires board.items[player.position().x][player.position().y].isCanStepOn();
  //@ ensures this.board == board;
  //@ ensures this.player == player;
  Game ( /*@ non_null @*/ Board board, /*@ non_null @*/ Player player) {
    this.board = board;
    this.player = player;
  }

  /** Check for the win situation - all marked positions have to have boxes on top. */
  /*@ ensures \result ==> gameWon;
    @*/
  /*@ pure @*/ boolean wonGame () {
    boolean result = true;
    /*@ loop_invariant x >= 0 && x <= board.xSize;
      @ loop_invariant result ==>
      @     (\forall int ix; ix>=0 && ix < x;
      @     (\forall int y; y>=0 && y < board.ySize;
      @       board.items[ix][y]._isMarked ==> (board.items[ix][y] instanceof Crate)));
      @ //         checkWonRow(board.items[ix]));
      @ decreases board.xSize - x;
      @*/
    for (int x = 0; x < board.xSize; x++) {
      if (!checkWonRow (board.items[x])) {
        result = false;
        break;
      }
    }
    return result;
  }

  /** Helper method for the above, ESC/Java2 does not deal well with nested loops.
    */
  /*@ requires row.length == board.ySize;
    @ requires (\forall int y; y>=0 && y < board.ySize; row[y] != null); 
    @ ensures \result ==> 
    @    (\forall int y; y>=0 && y < board.ySize;
    @       row[y]._isMarked ==> (row[y] instanceof Crate));
    @*/
  private /*@ pure @*/ boolean checkWonRow ( /*@ non_null @*/ BoardItem[] row) {
    boolean result = true;
    /*@ loop_invariant y>=0 && y<= board.ySize;
      @ loop_invariant result ==>
      @     (\forall int iy; iy>=0 && iy < y; 
      @         row[iy]._isMarked ==> (row[iy] instanceof Crate));
      @ decreases board.ySize - y;
      @*/
    for (int y = 0; y < board.ySize; y++) {
      if (row[y].isMarked () && !(row[y] instanceof Crate)) {
        result = false;
        break;
      }
    }
    return result;
  }

  /** The core of the game. Checks the validity of the move,
    *  moves the player to new position, rearranges the board
    *  accordingly.
    */
  //@ requires player.position().isValidNextPosition(newPosition);
  //@ ensures \result <==> player.position().equals(newPosition);
  /* @ normal_behavior
    @   requires !player.position().isValidNextPosition(newPosition);
    @   ensures !\result && \old(player.position()) == player.position();
    @   assignable \everything;
    @ also
    @ normal_behavior
    @   requires player.position().isValidNextPosition(newPosition);
    @   requires board.items[newPosition.x][newPosition.y].isCanStepOn();
    @   ensures \result && player.position() == newPosition;
    @   assignable \everything;
    @*/
  boolean movePlayer ( /*@ non_null @*/ Position newPosition) {
    // Check of the new position is on the board:
    //@ assert newPosition.x >= 0 && newPosition.x < board.xSize;
    //@ assert newPosition.y >= 0 && newPosition.y < board.ySize;
    // First a light check if the move is allowed
    if (!player.position ().isValidNextPosition (newPosition)) {
      return false;
    }
    // If the new position is ground just move
    if (board.items[newPosition.x][newPosition.y].isCanStepOn ()) {
      player.setPosition (newPosition);
      return true;
    }
    // Then, if the new position is occupied by something solid, skip
    if (!board.items[newPosition.x][newPosition.y].isMovable ()) {
      return false;
    }
    // Last case, it has to be something movable, check that
    // and make the move together with the item if possible:
    //@ assert board.items[newPosition.x][newPosition.y].isMovable();
    int xShift = newPosition.x - player.position ().x;
    int yShift = newPosition.y - player.position ().y;
    // The new position of the moved item:
    int nX = newPosition.x + xShift;
    int nY = newPosition.y + yShift;
    // See if we end up outside of the board and that the crate can be moved
    if (!(nX >= 0 && nX < board.xSize && nY >= 0 && nY < board.ySize)
	|| !board.items[nX][nY].isCanStepOn ()) {
      return false;
    }
    // Move the crate, change markings accordingly.
    Position newCratePosition = new Position (nX, nY);
    boolean wasMarked = board.items[newPosition.x][newPosition.y].isMarked ();
    boolean newMarked =
      board.items[newCratePosition.x][newCratePosition.y].isMarked ();

    board.items[newCratePosition.x][newCratePosition.y] = newMarked ?
      new MarkedCrate (newCratePosition) : new Crate (newCratePosition);
    board.items[newPosition.x][newPosition.y] = wasMarked ?
      new MarkedGround (newPosition) : new Ground (newPosition);

    player.setPosition (newPosition);
    return true;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString (){
    String r = "Game[ ";
    for (int x = 0; x < board.xSize; x++) {
      for (int y = 0; y < board.ySize; y++) {
        r += board.items[x][y] + ", ";
      }
    }
    r += player.toString () + " ]";
    return r;
  }

  public static void main (String[] args) {
    Board b = new Board (9, 9);
    for (int i = 0; i<9; i++) {
        b.putItemOnBoard (new Wall (new Position (0, i)));
        b.putItemOnBoard (new Wall (new Position (8, i)));
    }
    for (int i = 1; i<8; i++) {
        b.putItemOnBoard (new Wall (new Position (i, 0)));
        b.putItemOnBoard (new Wall (new Position (i, 8)));
    }
    for (int i = 1; i<8; i+=2) {
        b.putItemOnBoard (new Crate (new Position (1, i)));
        b.putItemOnBoard (new Crate (new Position (7, i)));
    }
    b.putItemOnBoard (new Crate (new Position (3, 1)));
    b.putItemOnBoard (new Crate (new Position (5, 1)));
    b.putItemOnBoard (new Crate (new Position (3, 7)));
    b.putItemOnBoard (new Crate (new Position (5, 7)));
    for (int i = 2; i<=6; i+=2) {
        b.putItemOnBoard (new Crate (new Position (2, i)));
        b.putItemOnBoard (new Crate (new Position (6, i)));
        b.putItemOnBoard (new MarkedGround (new Position (1, i)));
        b.putItemOnBoard (new MarkedGround (new Position (7, i)));
    }
    Player p = new Player (new Position (4, 4));
    Game g = new Game (b, p);
//    new GameGUI (g);		// NOTE comment this out for JMLUnitNG part of the homework
  }
}
