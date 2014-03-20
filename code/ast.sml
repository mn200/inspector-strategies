(* AST for inspectors and executors
 *     and an interpreter for them
 *     and a C code generator
 *)

use "primitives.sig";
use "primitives.sml";
use "environment.sml";

open primitives
open environment

datatype astnode =
         (* Define statement in a 1D loop *)
         (* write idx function, read idx functions, val compute, array *)
         (* A[ wf(i) ] = vf( A[ rf0(i) ], A[ rf1(i) ], ... ) *)
         AssignStmt of string                   (* iterator name *)  
                       * (int -> int)           (* wf         *)
                       * (int -> int) list      (* rf list    *)
                       * ((real list) -> real)  (* vf         *)
                       * string                 (* array name *)

         (* for ( lb <= i < ub ) body *)
         | ForLoop of string * int * int * astnode

         (* iterations of loop can be executed concurrently *)
         (* for ( lb <= i < ub ) body *)
         | ParForLoop of string * int * int * astnode

         (* Statement sequencing *)
         (* FIXME: right now just does two statements, but should have list *)
         | SeqStmt of astnode * astnode

(**** Interpreter ****)
(* Given the AST and the current environment, evaluates the AST
 * and returns a new updated environment. *)
fun eval ast env =
    case ast of
        (* Looks up current value of data array and iterator and then updates
         * a location in the data array based on write function, reads,
         * and the value function that computes the rhs of define stmt.
         *)
        AssignStmt (itername, wf,rfs,vf,Aname) =>
        let
            val i = vlookup (env, itername)
            val Aval = dlookup (env, Aname)
            val rhs = vf (map (fn rf => dsub(Aval,(rf i))) rfs) 
        in
            denvupdate(env, Aname, dupdate(Aval, wf i, rhs))
        end

      (* Right now the interpretation of ForLoop assumes lb=0. *)
      | ForLoop (itername,lb,ub,bodyast) =>
        FOR (0,ub)
            (fn iterval => fn env =>
                let 
                    val env = venvupdate(env, itername, iterval)
                in 
                    eval bodyast env
                end)
            env

      (* Right now the interpretation of ForLoop assumes lb=0. *)
      (* FIXME: need some way of doing random ordering of evaluations to
       * model concurrency. *)
      | ParForLoop (itername,lb,ub,bodyast) =>
        FOR (0,ub)
            (fn iterval => fn env =>
                let 
                    val env = venvupdate(env, itername, iterval)
                in 
                    eval bodyast env
                end)
            env

      | SeqStmt (s1,s2) =>
        eval s2 (eval s1 env)
