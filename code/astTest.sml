(* Testing for inspector and executor AST *)
use "primitives.sig";
use "primitives.sml";

use "ast.sml";

open primitives

exception TooManyReads

val defineSample = Define ((fn i : int => i),
                           [ fn i : int => i ],
                           (fn xs => case xs of 
                                         [] => raise List.Empty
                                       | x::[] => x + 1.0
                                       | _ => raise TooManyReads),
                           empty_dv (5, 0.0))

(* for (i=0; i<5; i++) { A[i] = A[i] + 1; } *)
val incrLoop = ForLoop ( 0, 5,
                         Define (
                             (fn i : int => i),
                             [ fn i : int => i ],
                             (fn xs => case xs of 
                                           [] => raise List.Empty
                                         | x::[] => x + 1.0
                                         | _ => raise TooManyReads),
                             empty_dv (5, 0.0)))
