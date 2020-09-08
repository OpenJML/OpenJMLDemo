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

  //@ public invariant 0 <= player.position.x && player.position.x < board.xSize && 0 <= player.position.y && player.position.y < board.ySize;
  // The player is in the valid playing area and not on a crate
  //@ public invariant board.ground[player.position.x][player.position.y];
  //@ public invariant !board.crate[player.position.x][player.position.y];

  // open is true for a position x,y if the position is part of the board
  // but does not have a crate on it
  //@ ensures \result == (x >= 0 && x < board.xSize && y >= 0 && y < board.ySize && board.ground[x][y] && ! board.crate[x][y]);
  //@ pure
  public boolean open(int x, int y) {
      return x >= 0 && x < board.xSize && y >= 0 && y <board.ySize && board.ground[x][y] && ! board.crate[x][y];
  }

  //@ ensures \result == ( x >= 0 && x < bbbbb.xSize && y >= 0 && y < bbbbb.ySize && bbbbb.ground[x][y] && ! bbbbb.crate[x][y]);
  //@ pure
  public static boolean open(Board bbbbb, int x, int y) {
      return x >= 0 && x < bbbbb.xSize && y >= 0 && y <bbbbb.ySize && bbbbb.ground[x][y] && ! bbbbb.crate[x][y];
  }

  //@ public model boolean gameStuck;
  // NOTE: Use the following form, once method calls within quanrtified statements are allowed;
  // instead we inline the metehod below
  /* @ public represents gameStuck = (\forall int x; x >= 0 && x < board.xSize; (\forall int y; y >= 0 && y < board.ySize;
  @    board.crate[x][y] ==>
  @      (
  @       !( open(x-1,y) && open(x+1,y) )
  @      &&
  @       !( open(x,y-1) && open(x,y+1) )
  @      )
  @ ));
  @*/
  /*@ public represents gameStuck = (\forall int x; x >= 0 && x < board.xSize; (\forall int y; y >= 0 && y < board.ySize;
  @    board.crate[x][y] ==> (
  @      !(
  @       ( x-1 >= 0 && x-1 < board.xSize && y >= 0 && y <board.ySize && board.ground[x-1][y] && ! board.crate[x-1][y]) 
  @       &&  
  @       ( x+1 >= 0 && x+1 < board.xSize && y >= 0 && y <board.ySize && board.ground[x+1][y] && ! board.crate[x+1][y]) 
  @       )
  @      &&
  @      !(
  @       ( x >= 0 && x < board.xSize && y-1 >= 0 && y-1 <board.ySize && board.ground[x][y-1] && ! board.crate[x][y-1]) 
  @       &&  
  @       ( x >= 0 && x < board.xSize && y+1 >= 0 && y+1 <board.ySize && board.ground[x][y+1] && ! board.crate[x][y+1]) 
  @       )
  @      )));
  @*/
  //@ public invariant !gameWon ==> !gameStuck;

  //@ public model boolean gameWon;
  /*@ public represents gameWon =
    @      (\forall int x; x>=0 && x < board.xSize;
    @          (\forall int y; y>=0 && y < board.ySize;
    @               board.marked[x][y] ==> board.crate[x][y] )); 
    @*/

  /** Create new game */
  //@ requires bbb.onBoard(player.position);
  //@ requires open(bbb,player.position.x,player.position.y);
  //@ ensures this.board == bbb;
  //@ ensures this.player == player;
  //@ pure
  Game ( /*@ non_null @*/ Board bbb, /*@ non_null @*/ Player player) {
    this.board = bbb;
    this.player = player;
  }

  /** Check for the win situation - all marked positions have to have boxes on top. */
  /*@ ensures \result <==> gameWon;
    @*/
  /*@ pure @*/ boolean wonGame () {
      boolean result = true;
    /*@ loop_invariant x >= 0 && x <= board.xSize;
      @ loop_invariant
      @     result == (\forall int ix; ix>=0 && ix < x;
      @       (\forall int y; y>=0 && y < board.ySize;
      @          (board.marked[ix][y] ==> board.crate[ix][y])));
      @ decreases board.xSize - x;
      @*/
    for (int x = 0; result && x < board.xSize; x++) {
        boolean rowresult = true;
    	/*@ loop_invariant
    	@       0 <= y && y <= board.ySize &&
        @       rowresult == (\forall int iy; iy>=0 && iy<y;
        @          (board.marked[x][iy] ==> board.crate[x][iy]));
        @ decreases board.ySize - y;
        @*/
        for (int y = 0; rowresult && y < board.ySize; y++) {
            if (board.marked[x][y] && !board.crate[x][y]) {
              rowresult = false; 
            }
        }
        result = rowresult;
    }
    return result;
  }
  
  // TODO: Should have a specification, and then will need better loop invariants
  /*@ pure */ boolean stuckGame() {
	    /*@ loop_invariant x >= 0 && x <= board.xSize;
      @ decreases board.xSize - x;
      @*/
    for (int x = 0; x < board.xSize; x++) {
        /*@ loop_invariant y >= 0 && y <= board.ySize;
        @ decreases board.ySize - y;
        @*/
        for (int y = 0; y < board.ySize; y++) {
            if (board.crate[x][y]) {
              if ((open(x-1,y)&&open(x+1,y)) || (open(x,y-1)&&open(x,y+1))) {
            	  return false;
              }
              
            }
        }
    }
    return true;
  }

  /** The core of the game. Checks the validity of the move,
    *  moves the player to new position, rearranges the board
    *  accordingly.
    */
  /*@ normal_behavior
    @   requires !player.position.isValidNextPosition(newPosition) || !board.onBoard(newPosition);
    @   ensures !\result && \old(player.position) == player.position;
    @   assignable \nothing;
    @ also
    @ normal_behavior
    @   requires player.position.isValidNextPosition(newPosition);
    @   requires board.onBoard(newPosition);
    @   requires !board.ground[newPosition.x][newPosition.y];
    @   assignable \nothing;
    @   ensures !\result && \old(player.position) == player.position;
    @ also
    @ normal_behavior
    @   requires player.position.isValidNextPosition(newPosition);
    @   requires board.onBoard(newPosition);
    @   requires board.ground[newPosition.x][newPosition.y];
    @   requires !board.crate[newPosition.x][newPosition.y];
    @   assignable player.position;
    @   ensures \result;
    @   ensures player.position == newPosition;
    @ also
    @ normal_behavior
    @   requires player.position.isValidNextPosition(newPosition);
    @   requires board.onBoard(newPosition);
    @   requires board.ground[newPosition.x][newPosition.y];
    @   requires board.crate[newPosition.x][newPosition.y];
    @   assignable \everything; // FIXME - could be more restrictive
//    @   ensures \result;
//    @   ensures player.position == newPosition;
    @      // FIXME - ensures crate moves properly
    @*/
  boolean movePlayer ( /*@ non_null @*/ Position newPosition) {
    // First a light check if the move is allowed and the position is OK
    if (!player.position.isValidNextPosition (newPosition) || !board.onBoard(newPosition)) {
      return false;
    }
    // Check if the new position is on the board:
    //@ assert newPosition.x >= 0 && newPosition.x < board.xSize;
    //@ assert newPosition.y >= 0 && newPosition.y < board.ySize;
    // If it is not ground, then it is off the playable area
    if (!board.ground[newPosition.x][newPosition.y]) {
        return false;
      }
    // If the new position is not a crate just move
    if (!board.crate[newPosition.x][newPosition.y]) {
        //@ assert board.onBoard(newPosition);
      player.setPosition (newPosition);
      return true;
    }

    // Last case, it has to be something movable, check that
    // and make the move together with the item if possible:
    //@ assert board.crate[newPosition.x][newPosition.y];
    //@ assert board.ground[newPosition.x][newPosition.y];
    int xShift = newPosition.x - player.position.x;
    int yShift = newPosition.y - player.position.y;
    // The new position of the moved item:
    int nX = newPosition.x + xShift;
    int nY = newPosition.y + yShift;
    //@ assert board.ground[newPosition.x][newPosition.y];
    // See if the new position for the crate is OK
    if (!board.onBoard(nX,nY) || !open(nX,nY)) {
      return false;
    }
    //@ assert nX != newPosition.x || nY != newPosition.y;
    //@ assert board.ground[newPosition.x][newPosition.y];

    //@ assume board.ground != board.crate;

    // Move the crate, change markings accordingly.
    board.crate[newPosition.x][newPosition.y] = false; // old position of crate
    board.crate[nX][nY] = true; // new position of crate

    //@ assume nX != player.position.x || nY != player.position.y;
    //@ assume nX != newPosition.x || nY != newPosition.y;
    //@ assert board.ground[newPosition.x][newPosition.y];
    //@ assert !board.crate[newPosition.x][newPosition.y];
    player.setPosition (newPosition);
    return true;
  }

  //@ skipesc
  boolean movePlayerMultiStep ( /*@ non_null @*/ Position newPosition) {
	    if (!player.position.isValidNextPositionMultiStep (newPosition)) {
	        return false;
	    }
	    if (player.position.x < newPosition.x) {
	    	for (int i = player.position.x+1; i<=newPosition.x; i++ )
	    		if (!movePlayer(new Position(i,player.position.y))) return false;
	    } else if (player.position.x > newPosition.x) {
	    	for (int i = player.position.x-1; i>=newPosition.x; i-- )
	    		if (!movePlayer(new Position(i,player.position.y))) return false;
	    } else if (player.position.y > newPosition.y) {
	    	for (int i = player.position.y-1; i>=newPosition.y; i-- )
	    		if (!movePlayer(new Position(player.position.x,i))) return false;
	    } else if (player.position.y < newPosition.y) {
	    	for (int i = player.position.y+1; i<=newPosition.y; i++ )
	    		if (!movePlayer(new Position(player.position.x,i))) return false;
	    } else {
	    	return false;
	    }
	    return true;
  }

  //@ skipesc
  public /*@ non_null @*/ String toString (){
    String r = "Game[ ";
    for (int x = 0; x < board.xSize; x++) {
      for (int y = 0; y < board.ySize; y++) {
        r += board.crate[x][y] + ", "; // FIXME - needs fixing up
      }
    }
    r += player.toString () + " ]";
    return r;
  }

  public static void main (String[]args) {
    Player p = new Player (new Position (4, 4));
    Board b = new Board (9, 9);
    //@ loop_invariant 1 <= x && x <=8;
    for (int x = 1; x < 8; x++) {
        //@ loop_invariant 1 <= y && y <=8;
    	for (int y=1; y<8; y++)
    		b.ground[x][y] = true;
    }
    b.crate[1][1] = true;
    b.crate[1][3] = true;
    b.crate[1][5] = true;
    b.crate[1][7] = true;
    b.crate[7][1] = true;
    b.crate[7][3] = true;
    b.crate[7][5] = true;
    b.crate[7][7] = true;
    b.crate[3][1] = true;
    b.crate[5][1] = true;
    b.crate[3][7] = true;
    b.crate[5][7] = true;
    b.crate[1][3] = true;
    b.crate[1][5] = true;
    b.crate[2][2] = true;
    b.crate[2][4] = true;
    b.crate[2][6] = true;
    b.crate[6][2] = true;
    b.crate[6][4] = true;
    b.crate[6][6] = true;
    b.marked[1][2] = true;
    b.marked[1][4] = true;
    b.marked[1][6] = true;
    b.marked[7][2] = true;
    b.marked[7][4] = true;
    b.marked[7][6] = true;
    Game g = new Game (b, p);
    new GameGUI (g);		// NOTE comment this out for JMLUnitNG part of the homework
  }
}
