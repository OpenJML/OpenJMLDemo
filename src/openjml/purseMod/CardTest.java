

public class CardTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {

		// declare variables
		int owner = 23; 
		Terminal terminal = new Terminal(owner);
		Card card = new Card();
		
		// Error 1 detected:
		// JMLInternalExceptionalPostconditionError: by method Card.Card regarding specifications at
		// File "..\..\..\workspace\Assignment 1\src\purse\Card.java", line 123, character 35, when
		// thrown is java.lang.ArrayIndexOutOfBoundsException: 4
		// at purse.CardTest.main(CardTest.java:303)
		// -> violation of signals (Exception) false;
		
		// fix 1: correct bounds for for-loops
		
		// rerun
		
		// Error 2 detected
		// JMLInvariantError: by method Card.<init>@post<File "..\..\..\workspace\Assignment 1\src\purse\Card.java", line 124, character 16>
		// at purse.Card.checkInv$instance$Card(Card.java:369)
		// at purse.Card.<init>(Card.java:156)
		// at purse.CardTest.internal$main(CardTest.java:13)
		// at purse.CardTest.main(CardTest.java:287)
		// -> violation of invariant amount >= 0;
		
		// fix 2: change initialisation of amount
		// alternative fix: add condition states != UNINIT ==> amount >= 0

		// rerun and continue
		
		// insert card in terminal
		
		terminal.insertCard(card);
		
        // note there is an error in clearPin(), called in insertCard(), but this is not detected here,
		// because all elements in pin_pos are still at their initial values
		
		// enter value to initialise pin code (1 2 3 4 5 6 7 8)
		for (byte i = 0; i < 8; i++){
			terminal.enterDigit(i);
		}
		
		// initialise card
		try {terminal.initCard();} catch (Exception e) {};
		
		// make 16 loads (tokens fit in original loaded array)
		for (int i = 0; i < 16; i++) {
			try {terminal.load(i);} catch (Exception e) {};
		} 
		
		// Error 3 detected
		// JMLInternalNormalPostconditionError: by method Token.sign
		// at purse.Token.sign(CardTest.java:1330)
		// at purse.Terminal.load(Terminal.java:169)
		// at purse.CardTest.internal$main(CardTest.java:1824)
		// at purse.CardTest.main(CardTest.java:2107)
		// -> violation of ensures check(key1, key)
		
		// fix 3: change implementation of sign, to match check
		
		// rerun and continue 
		
		// make 17th load, loaded array should be expanded
		try {terminal.load(24);} catch (Exception e) {};
		
		// Error 4 detected
		// JMLInternalExceptionalPostconditionError: by method Card.append regarding specifications at
		// File "..\..\..\workspace\Assignment 1\src\purse\CardTest.java", line 211, character 43, when
		//	thrown is java.lang.ArrayIndexOutOfBoundsException: 16
		// at purse.Card.load(CardTest.java:4915)
		// at purse.Terminal.load(Terminal.java:170)
		// at purse.CardTest.internal$main(CardTest.java:7718)
		// at purse.CardTest.main(CardTest.java:7994)
        // -> violation of signals (Exception) false;

		// fix 4: change condition in append to be i >= array.length

		// rerun and continue
		
		// make payment
		try {terminal.pay(26);} catch (Exception e) {};
		
		// Error 5 detected
		
		// JMLInternalNormalPostconditionError: by method Card.pay
		// at purse.Card.pay(CardTest.java:5279)
		// at purse.Terminal.internal$pay(CardTest.java:6331)
		// at purse.Terminal.pay(CardTest.java:9048)
		// at purse.CardTest.internal$main(CardTest.java:11941)
		// at purse.CardTest.main(CardTest.java:12223)
		// -> violation of postcondition
        // ensures (\exists int i; 0 <= i && i < payed.length; payed[i] != null &&
        // payed[i].getAmount() == amount &&
        // payed[i].getOwner() == payee);
		
		// fix 5: append payment token to payed

		// rerun and continue
		
		// remove card from terminal and insert it again
		terminal.ejectCard();
		terminal.insertCard(card);
		
		// Error 6 detected
		// JMLInternalExceptionalPostconditionError: by method Terminal.clearPin regarding specifications at
		// File "..\..\..\workspace\Assignment 1\src\purse\CardTest.java", line 504, character 41, when
		//	thrown is java.lang.ArrayIndexOutOfBoundsException: 8
		// at purse.Terminal.insertCard(CardTest.java:7821)
		// at purse.CardTest.internal$main(CardTest.java:11899)
		// at purse.CardTest.main(CardTest.java:12171)
        // -> violation of signals (Exception) false;
		
		// fix 6: change order of the two statements

		// rerun and continue
		
		// enter incorrect pincode
		for (int i = 0; i < 8; i++){
			terminal.enterDigit((byte)1);
		}

		// make 2 pay attempts with incorrect pin code
		
		try {terminal.pay(1);} catch (CardException e){};
		try {terminal.pay(1);} catch (CardException e){};		
		
		// make 3rd pay attempt with incorrect pin code -> card becomes temporarily blocked
		try {terminal.pay(1);} catch (CardException e){};
		
		// JMLInternalExceptionalPostconditionError: by method Card.pay regarding specifications at
		// File "..\..\..\workspace\Assignment 1\src\purse\CardTest.java", line 323, character 58, when
		//	thrown is purse.CardException: invalid pin
		// at purse.Terminal.pay(CardTest.java:9039)
		// at purse.CardTest.internal$main(CardTest.java:11937)
		// at purse.CardTest.main(CardTest.java:12213)
		// -> violation of
		//   signals (CardException) basic_attempts == 3 ? status == TEMP_BLOCKED : status == \old(status);

		// original implementation: card only gets blocked when pay is called for 4th time
		// and even gets blocked when the pin code is correct at this 4th attempt
		
		// fix: change code to first check pin code, then increase basic attempts
		// temporarily block card when basic_attempts becomes 3

		// notice: same fix necessary for unlock
		
		// rerun and continue

		// the card is blocked now
		
		// try to unlock with incorrect pin code
		
		try {terminal.unlock();} catch (CardException e) {};
		
		// change pin code to correct pin code
		terminal.clearPin();
		for (byte i = 0; i < 8; i++){
			terminal.enterDigit(i);
		}
		
		// successful unlock
		try {terminal.unlock();} catch (CardException e) {};
		
		// Error 8 
		
		// JMLInternalNormalPostconditionError: by method Card.unlock
		// at purse.Card.unlock(CardTest.java:5534)
		// at purse.Terminal.internal$unlock(CardTest.java:6309)
		// at purse.Terminal.unlock(CardTest.java:9294)
		// at purse.CardTest.internal$main(CardTest.java:11953)
		// at purse.CardTest.main(CardTest.java:12229)
        // -> violation of  ensures master_attempts == 0;
		
		// fix: add missing assignment
		
		// No the whole application completes successfully
		

	}

}
