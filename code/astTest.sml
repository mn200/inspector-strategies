(* Testing for inspector and executor AST *)
use "primitives.sig";
use "primitives.sml";

use "ast.sml";

open primitives

exception TooManyReads

val defineSample = DefineStmt ("i",
                               (fn i : int => i),
                               [ fn i : int => i ],
                               (fn xs => case xs of 
                                             [] => raise List.Empty
                                           | x::[] => x + 1.0
                                           | _ => raise TooManyReads),
                               "A")

(* for (i=0; i<5; i++) { A[i] = A[i] + 1; } *)
val incrLoop = ForLoop ( "i", 0, 5,
                         DefineStmt (
                             "i",
                             (fn i : int => i),
                             [ fn i : int => i ],
                             (fn xs => case xs of 
                                           [] => raise List.Empty
                                         | x::[] => x + 1.0
                                         | _ => raise TooManyReads),
                             "A"))

val initStmt = DataInit ( "A", 5, 0.0 )

(* Example computation
 * A[i] = 0.0, forall i in [0,5)
 * for (i=0; i<5; i++)
 *   A[i] = A[i] + 1
 *)
val comp_incr = SeqStmt( initStmt, incrLoop )

val comp_incr_test = dvector_to_list (dlookup ((eval comp_incr empty_env),"A"))
