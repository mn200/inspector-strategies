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
         DefineStmt of (int -> int)             (* wf         *)
                       * (int -> int) list      (* rf list    *)
                       * ((real list) -> real)  (* vf         *)
                       * string                 (* array name *)

         (* for ( lb <= i < ub ) *)
         | ForLoop of int * int * astnode

         (* data array declaration and initialization  *)
         | DataInit of string                (* name            *)
                       * int                 (* domain is [0,N) *) 
                       * real                (* initial value   *)

(* environment maps names to values *)
(* values are of types in the primitives module like dvector, ivector, etc. *)
(* how do we do this because of polymorphism issue? guess one dictionary
   for each type? *)
(* where should I put the definition of the dictionary, environment, 
   and the interpreter? *)
type 'a dict = string -> 'a option

val empty_dict : 'a dict = fn key => NONE

fun insert (key, value) d = fn s => if s=key
                                    then SOME value
                                    else d s

fun lookup key d = d key

val env = { datadict = empty_dict, indexdict = empty_dict }

val datadict = empty_dict

(* Interpreter *)
(* Given the AST and the current environment, evaluates the AST
 * and returns a new updated environment. *)
(*
fun eval t env =
    case t of
        DefineStmt wf rfs vf Aname => let Aval = lookup Aname datadict
                                          i = iter env
                                          rhs = vf i map (fn rf => dsub Aval (rf i) rfs 
                                      in
                                          env_dupdate Aname dupdate (Aval, wf i, rhs)
                                                          end
*)
