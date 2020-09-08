import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

//@ skiprac
class GameGUI {

    //@ skipesc 
  GameGUI (Game g) {
    JPanel gamePanel = new MyPanel (g);
    JFrame f = new JFrame ("Sokoban");
    gamePanel.setFocusable (true);
    gamePanel.grabFocus ();
    f.setSize (new Dimension (g.board.xSize * MyPanel.ICON_W,
      g.board.ySize * MyPanel.ICON_H + 30));
    f.setDefaultCloseOperation (JFrame.EXIT_ON_CLOSE);
    f.getContentPane ().add (gamePanel);
    f.setLocationRelativeTo (f.getRootPane ());
    f.setVisible (true);
  }

  public class MyPanel extends JPanel {
    private static final long serialVersionUID = 5873729837228423326L;

    static final int ICON_W = 32;
    static final int ICON_H = 32;

    Game game;
    BufferedImage playerImage, wallImage, crateImage, crateMarkedImage, blankImage, blankMarkedImage;
    boolean informed = false;

    //@ skipesc
    public MyPanel (Game g) {
      super ();
      this.game = g;
      this.addMouseListener (new MouseAdapter () {
        public void mouseClicked (MouseEvent me) {
          Point p = me.getPoint ();
          if (game.movePlayerMultiStep (new Position (p.x / ICON_W, p.y / ICON_H))) {
            repaint ();
            check();
          }
        }
      });
      this.addKeyListener (new KeyAdapter () {
        public void keyPressed (KeyEvent ke) {
          int key = ke.getKeyCode ();
          int dx = 0, dy = 0;
          if (key == KeyEvent.VK_DOWN) dy++;
          else if (key == KeyEvent.VK_UP) dy--;
          else if (key == KeyEvent.VK_RIGHT) dx++;
          else if (key == KeyEvent.VK_LEFT) dx--;
          if (dx != 0 || dy != 0) {
            int nx = game.player.position.x + dx;
            int ny = game.player.position.y + dy;
            if (nx >=0 && nx < game.board.xSize && ny >=0 && ny < game.board.ySize && game.movePlayer (new Position (nx, ny))) {
              repaint ();
              check();
            }
          }
        }
      });
      try {
          playerImage = ImageIO.read (new File ("icons/player.png"));
          blankImage = ImageIO.read (new File ("icons/blank.png"));
          blankMarkedImage = ImageIO.read (new File ("icons/blankmarked.png"));
          crateImage = ImageIO.read (new File ("icons/crate.png"));
          crateMarkedImage = ImageIO.read (new File ("icons/cratemarked.png"));
          wallImage = ImageIO.read (new File ("icons/wall.png"));
      } catch (IOException e1) {
          try {
              playerImage = ImageIO.read (getClass ().getResource ("player.png"));
              blankImage = ImageIO.read (getClass ().getResource ("blank.png"));
              blankMarkedImage = ImageIO.read (getClass ().getResource ("blankmarked.png"));
              crateImage = ImageIO.read (getClass ().getResource ("crate.png"));
              crateMarkedImage = ImageIO.read (getClass ().getResource ("cratemarked.png"));
              wallImage = ImageIO.read (getClass ().getResource ("wall.png"));
          } catch (IOException e2) {
              System.out.println ("Icon files not found!");
              System.exit (1);
          }
      }
    }
    
    //@ skipesc
    public void check() {
        if (!informed && game.wonGame ()) {
            JOptionPane.showMessageDialog (MyPanel.this, "You won!");
            informed = true;
          }
        if (!informed && game.stuckGame ()) {
            JOptionPane.showMessageDialog (MyPanel.this, "You are stuck!");
            informed = true;
          }
    }

    //@ skipesc
    public void paintComponent (Graphics g) {
      Graphics2D g2 = (Graphics2D) g;

      for (int y = 0; y < game.board.ySize; y++) {
        for (int x = 0; x < game.board.xSize; x++) {
          BufferedImage image = null;

          if (game.player.position.equals (new Position (x, y))) {
            image = playerImage;
          } else {
            if (game.board.items[x][y].crate)
                  image = game.board.items[x][y].marked? crateMarkedImage : crateImage;
            else if (game.board.items[x][y].ground)
                image = game.board.items[x][y].marked? blankMarkedImage : blankImage;
            else
              image = wallImage;
          }
	      g2.drawImage (image, null, x * ICON_W, y * ICON_H);
        }
      }
    }
  }
}
