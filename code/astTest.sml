(* Testing for inspector and executor AST *)
use "primitives.sig";
use "primitives.sml";

use "ast.sml";

open primitives

exception TooManyReads

val defineSample = AssignStmt ("i",
                               (fn i : int => i),
                               [ fn i : int => i ],
                               (fn xs => case xs of x::[] => x + 1.0),
                               "A")

(* for (i=0; i<5; i++) { A[i] = A[i] + 1; } *)
val incrLoop = ForLoop ( "i", 0, 5,
                         AssignStmt (
                             "i",
                             (fn i : int => i),
                             [ fn i : int => i ],
                             (fn xs => case xs of x::[] => x + 1.0),
                             "A"))

(* for (i=0; i<5; i++) { A[i] = A[i] + 1; } *)
val parincrLoop = ParForLoop ( "i", 0, 5,
                         AssignStmt (
                             "i",
                             (fn i : int => i),
                             [ fn i : int => i ],
                             (fn xs => case xs of x::[] => x + 1.0),
                             "A"))

val initStmt = DataInit ( "A", 5, 0.0 )

(* Example computation
 * A[i] = 0.0, forall i in [0,5)
 * for (i=0; i<5; i++)
 *   A[i] = A[i] + 1
 *)
val comp_incr = SeqStmt( initStmt, incrLoop )

val comp_incr_test = dvector_to_list (dlookup ((eval comp_incr empty_env),"A"))
  (* = [1.0,1.0,1.0,1.0,1.0], real lists are not equality types I guess*)

(* The parallel implementation of the above. *)
val comp_incr_par = SeqStmt( initStmt, parincrLoop )
val comp_incr_par_test = dvector_to_list (
        dlookup ((eval comp_incr_par empty_env),"A"))
