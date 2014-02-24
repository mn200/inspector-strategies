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
         DefineStmt of string                   (* iterator name *)  
                       * (int -> int)           (* wf         *)
                       * (int -> int) list      (* rf list    *)
                       * ((real list) -> real)  (* vf         *)
                       * string                 (* array name *)

         (* for ( lb <= i < ub ) body *)
         | ForLoop of string * int * int * astnode

         (* data array declaration and initialization  *)
         | DataInit of string                (* data array name *)
                       * int                 (* domain is [0,N) *) 
                       * real                (* initial value   *)

         (* Statement sequencing *)
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
        DefineStmt (itername, wf,rfs,vf,Aname) =>
        let
            val i = iterlookup (env, itername)
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
                    val env = iterenvupdate(env, itername, iterval)
                in 
                    eval bodyast env
                end)
            env
                    
      | DataInit (name,size,initval) =>
        denvupdate(env, name, empty_dv(size,initval))

      | SeqStmt (s1,s2) =>
        eval s2 (eval s1 env)
