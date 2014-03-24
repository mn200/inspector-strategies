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
val initEnv = denvupdate ( empty_env, "A", empty_dv(5,0.0) )

val comp_incr_test = dvector_to_list (dlookup ((evalstmt incrLoop initEnv),"A"))
  (* = [1.0,1.0,1.0,1.0,1.0], real lists are not equality types I guess*)

(* The parallel implementation of the above. *)
val comp_incr_par_test = dvector_to_list (
        dlookup ((evalstmt parincrLoop initEnv),"A"))

(* Some testing for the expression evaluation. *)
val gofi_exp = ISub("g", VarExp("i"))  (* g[i] *)

(* initialize environment with index array g and iterator i *)
val initEnv = venvupdate( ienvupdate( empty_env, "g", empty_iv(5,5)), "i", 3)

val gofi_exp_test = evaliexp gofi_exp initEnv
