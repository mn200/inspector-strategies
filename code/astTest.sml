(* Testing for inspector and executor AST *)
use "primitives.sig";
use "primitives.sml";

use "ast.sml";

open primitives

exception TooManyReads

(*val defineSample = AssignStmt ("i",
                               (fn i : int => i),
                               [ fn i : int => i ],
                               (fn xs => case xs of x::[] => x + 1.0),
                               "A")*)
val defineSample = AssignStmt ("A",VarExp("i"),
                               [ Read("A",VarExp("i")) ],
                               (fn xs => case xs of x::[] => x + 1.0))

(* for (i=0; i<5; i++) { A[i] = A[i] + 1; } *)
val incrLoop = ForLoop ( "i", 0, 5,
                         AssignStmt ("A",VarExp("i"),
                               [ Read("A",VarExp("i")) ],
                               (fn xs => case xs of x::[] => x + 1.0)))

(* for (i=0; i<5; i++) { A[i] = A[i] + 1; } *)
val parincrLoop = ParForLoop ( "i", 0, 5,
                         AssignStmt ("A",VarExp("i"),
                               [ Read("A",VarExp("i")) ],
                               (fn xs => case xs of x::[] => x + 1.0)))

(* Initialize the environment *)
(* A[i] = 0.0, forall i in [0,5) *)
val initEnv = envupdate ( empty_env, "A", RealVecVal(empty_dv(5,0.0)) )

val comp_incr_test = dvector_to_list (
        getrealvec( envlookup ((evalstmt incrLoop initEnv),"A") ) )
  (* = [1.0,1.0,1.0,1.0,1.0], real lists are not equality types I guess*)

(* The parallel implementation of the above. *)
val comp_incr_par_test = dvector_to_list (
        getrealvec( envlookup ((evalstmt parincrLoop initEnv),"A") ) )

(* Testing sequences of statements *)
val loopseq = SeqStmt([incrLoop,incrLoop])
val comp_incrincr_test = 
    dvector_to_list ( getrealvec( envlookup ((evalstmt loopseq initEnv),"A") ) )

(*****************************************************)
(* Some testing for the expression evaluation. *)
val gofi_exp = ISub("g", VarExp("i"))  (* g[i] *)

(* initialize environment with index array g and iterator i *)
val initEnv = envupdate( 
        envupdate( empty_env, "g", IVecVal(empty_iv(5,5))), "i", IntVal(3) )

val gofi_exp_test = evaliexp gofi_exp initEnv
