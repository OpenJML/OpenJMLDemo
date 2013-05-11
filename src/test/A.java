package test;
import org.jmlspecs.annotation.*;
public class A {

	//@ ensures \fresh(null); 
	public static void main(@NonNull String... args) {
		System.out.println("START");
		//@ assert false;  
		
		org.jmlspecs.utils.Utils.showStack = true;
		
		//@ assert args.length > 0 : "Has arguments";
		System.out.println("END");
	}
}
