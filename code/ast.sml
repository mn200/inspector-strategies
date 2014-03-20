(* AST for inspectors and executors
 *     and an interpreter for them
 *     and a C code generator
 *)

use "primitives.sig";
use "primitives.sml";
use "environment.sml";

open primitives
open environment

(* grammar for affine expressions with UFTerms *)
datatype expnode =
         (* iterator or parameter variable read *)
         VarExp of string

         (* index array read, e.g., f(i) *)
         | ISub of string * expnode

datatype daccess =
         Write of string * expnode
         | Read of string * expnode

datatype astnode =
         (* Define statement in a 1D loop *)
         (* write idx function, read idx functions, val compute, array *)
         (* A[ wf(i) ] = vf( A[ rf0(i) ], A[ rf1(i) ], ... ) *)
         AssignStmt of daccess                  (* wf         *)
                       * daccess list           (* rf list    *)
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

(* Since these are indexing expressions, the result of evaluating them is int*)
fun evalexp exp  env =
    case exp of

         (* iterator or parameter variable read *)
         VarExp id => vlookup(env, id)

         (* index array read, e.g., f(i) *)
         | ISub(id,e) => isub( ilookup(env,id), (evalexp e env) )

fun evaldaccess da env =
    case da of
        Write (id,exp) => evalexp exp env
      | Read (id,exp) => evalexp exp env

fun eval ast env =
    case ast of
        (* Looks up current value of data array and iterator and then updates
         * a location in the data array based on write function, reads,
         * and the value function that computes the rhs of define stmt.
         *)
        AssignStmt (wf,rfs,vf,Aname) =>
        let
            val Aval = dlookup (env, Aname)
            val rhs = vf (map (fn rf => dsub(Aval,(evaldaccess rf env))) rfs) 
        in
            denvupdate(env, Aname, dupdate(Aval, (evaldaccess wf env), rhs))
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

