(* AST for inspectors and executors
 *     and an interpreter for them
 *     and a C code generator
 *)

use "primitives.sig";
use "primitives.sml";
open primitives

datatype astnode =
         (* write idx function, read idx functions, val compute, array *)
         (* A[ wf(i) ] = vf( A[ rf0(i) ], A[ rf1(i) ], ... ) *)
         Define of (int -> int)             (* wf      *)
                   * (int -> int) list      (* rf list *)
                   * ((real list) -> real)  (* vf      *)
                   * real dvector           (* array *)

         (* for ( lb <= i < ub ) *)
         | ForLoop of int * int * astnode

