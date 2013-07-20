package loops;

public class EscTest {

    /*@ ensures \result == x+1 ; */
    public static int incr(int x){
        x++;
        return x;
    }
    
    /*@ normal_behavior
        requires ar != null ;
        //assignable ar[*];   // ADDED
      @ //ensures  all_zero(ar) ;// ADDED
      @ ensures (\forall int k ; 0 <= k && k < ar.length ; ar[k]==0 ) ;
     */
    public static void zero_array(int ar[]){
        int i=0;
        int N=ar.length;
        //@ loop_invariant 0<= i && i<=N ;
        //@ loop_invariant (\forall int k ; 0 <= k && k < i ; ar[k]==0 ) ;
        while(i<N){
            ar[i]=0;
            i++;
        }
    }
    
    /*@ normal_behavior
        requires ar != null ;
      @ ensures \result == (\forall int l ; 0 <= l && l < ar.length ; ar[l]==0 ) ;
     */
    /*@ pure helper */ public static boolean all_zero(int ar[]){ // ADDED helper
        int i=0;
        int N=ar.length;
        boolean res=true;
        //@ loop_invariant 0<= i && i<=N ;
        //@ loop_invariant res == (\forall int k ; 0 <= k && k < i ; ar[k]==0 ) ;
        while(i<N){
            if (ar[i]!=0) res=false;
            i++;
        }
        return res;
    }
    
    /*@ normal_behavior
        requires mat != null ;
        requires mat.length >0 ;
        requires (\forall int k ; 0 <= k && k < mat.length ; mat[k]!=null ) ;
      @ ensures (\forall int k ; 0 <= k && k < mat.length ; all_zero( mat[k] ) ) ;
     */
    public static void zero_matrix(int mat[][]){
        int i=0;
        //@ loop_invariant 0<= i && i<=mat.length && mat != null ;
        //  @ loop_invariant mat == \old(mat);
        //  @ loop_invariant (\forall int k ; 0 <= k && k < mat.length ; mat[k] == \old(mat[k]) ) ;
        //@ loop_invariant (\forall int k ; 0 <= k && k < mat.length ; mat[k]!=null ) ;
        //@ loop_invariant (\forall int k ; 0 <= k && k < i ; all_zero( mat[k] ) ) ;
        while(i<mat.length){
            //  @ assume (\forall int k ; 0 <= k && k < i ; all_zero( mat[k] ) ) ;
            //  @ assert i > 0 ==> all_zero(mat[0]);
        	a:{}
            zero_array(mat[i]);
            //  @ assume (\forall int k; 0<=k && k<i; (\forall int kk; 0<=kk && kk <mat[k].length; mat[k][kk] == \old(mat[k][kk],a)));
            //  @ assert all_zero(mat[i]);
            //  @ assert all_zero(mat[0]);
            i++;
        }
    }
    /*@ normal_behavior
        requires mat != null ;
        requires mat.length >0 ;
        requires (\forall int k ; 0 <= k && k < mat.length ; mat[k]!=null ) ;
      @ ensures (\forall int k ; 0 <= k && k < mat.length ; (\forall int l ; 0 <= l && l < mat[k].length ; mat[k][l]==0 ) ) ;
     */
    public static void zero_matrix_2(int mat[][]){
        int i=0;
        //@ loop_invariant 0<= i && i<=mat.length && mat != null ;
        //@ loop_invariant (\forall int k ; 0 <= k && k < mat.length ; mat[k]!=null ) ;
        //@ loop_invariant (\forall int k ; 0 <= k && k < i ; (\forall int l ; 0 <= l && l < mat[k].length ; mat[k][l]==0 ) ) ;
        while(i<mat.length){
            zero_array(mat[i]);
            i++;
            //@ reachable;
        }
    }


}

