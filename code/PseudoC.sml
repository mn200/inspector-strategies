(* PseudoC representation for inspectors and executors
 *     and a C code generator
 *)

(* Starting from hol/PseudoCScript.sml commit 41b8290
 *
 *     differences
 *         -only need scalar values in expressions, so no Array (value list)
 *         -don't need Error value because not interpreting
 *         -need deep embedding for operations for code generation
 *         -don't need to carry around memory in SeqStmt like in Seq because
 *          not interpreting
 *         -don't need Par, Abort, or Done because not interpreting
 *         -need 
 *)

datatype value =
         Int of int
         | Real of real
         | Bool of bool


datatype expr =
         (* scalar variable read *)
         VarExp of string

         (* index array read, e.g., f(i) *)
         | ISub of string* expr

         (* constant integer *)
         | Value of value

         (* operations needed so far for wavebench example *)
         | Max of expr * expr
         | Plus of expr * expr
         | Minus of expr * expr
         | Mult of expr * expr
         | Convert of expr  (* convert an integer to a double *)


datatype domain =
         D1D of expr * expr


(* Statements in PseudoC *)
datatype stmt =
         (* Array element define statement in input computation.
          * Reads and writes to arrays (where scalars are 1 element arrays)
          * are broken out to enable creation of the action/deps graph. *)
         DAssign of string * expr            (* write: array and index expr *)
                    * (string*expr) list     (* reads *)
                    * ((string*expr) list -> expr)  (* fun to plug in read exprs *)

         (* Array element define in inspector. *)
         | Assign of string * expr           (* write: array and index expr *)
                     * expr                  (* rhs *)

         (* Assignment to scalar *)
         | AssignVar of string * expr        (* var = rhs *)
(*
         (* Aname, index domain, range domain, initval *)
         | Malloc of string * domain * domain * tuple

         (* for ( lb <= i < ub ) body, for now just works for domain1D *)
         | ForLoop of string list * domain * stmt

         (* iterations of loop can be executed concurrently *)
         (* for ( lb <= i < ub ) body *)
         | ParForLoop of string list * domain * stmt

         (* Statement sequencing *)
         | SeqStmt of stmt list
*)

(**** Code Generator ****)
