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


(**** Interpreter ****)
datatype evalResult =
         Env of envtype 
       | LoopBody of int * envtype -> envtype

(* Given the AST and the current environment, evaluates the AST
 * and returns a new updated environment. *)
fun eval ast env =
    case ast of
        DefineStmt (wf,rfs,vf,Aname)
          => LoopBody 
                 (fn (i,env) =>
                    let 
                        val SOME Aval = dlookup (env, Aname)
                        val rhs = vf (map (fn rf => dsub(Aval,(rf i))) rfs) 
                    in
                        denvupdate (env,Aname,dupdate(Aval, wf i, rhs))
                    end)
      | ForLoop (lb,ub,bodyast) => Env env
      | DataInit (name,size,initval) => Env env
