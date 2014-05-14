(* AST for inspectors and executors
 *     and an interpreter for them
 *     and a C code generator
 *)

use "primitives.sig";
use "primitives.sml";
use "environment.sml";

open primitives
open environment

(* grammar for index expressions: affine expressions with UFTerms *)
datatype iexp =
         (* iterator or parameter variable read *)
         VarExp of string

         (* constant integer *)
         | Const of int

         (* index array read, e.g., f(i) *)
         | ISub of string * iexp

(* data expressions *)
datatype dexp =
         Convert of iexp
         | Read of string * iexp
         | DValue of real

(* Expressions in PseudoC. *)
datatype value =
         Int of int
         | Real of real
         | Array of value list
         | Bool of bool

(* FIXME: Want these to replace iexp above. *)
(*datatype expr = 
         VarExp of string
       | ISub of string * expr
       | Opn of (value list -> value ) * (expr list)
       | Value of value
*)

(* Statements in PseudoC *)
datatype stmt =
         (* Define statement in a 1D loop *)
         (* write idx function, functions, val compute, array   *)
         (* A[ wf(i) ] = vf( read0(i) ], read1(i) ], ... )      *)
         (* e.g. read#(i)=A[i], read#(i)=A[f[i]], or read#(i)=i *)
         AssignStmt of string * iexp            (* wf           *)
                       * dexp list              (* reads        *)
                       * ((real list) -> real)  (* vf           *)

         (* Assignment to scalar, global, or local. *)
         (*| AssignVar of string * expr*)

         (* Aname, index domain, range domain, initval *)
         | Malloc of string * domain * domain * tuple

         (* for ( lb <= i < ub ) body, for now just works for domain1D *)
         | ForLoop of string list * domain * stmt

         (* iterations of loop can be executed concurrently *)
         (* for ( lb <= i < ub ) body *)
         | ParForLoop of string list * domain * stmt

         (* Statement sequencing *)
         | SeqStmt of stmt list


(**** Interpreter ****)
(* Given the AST and the current environment, evaluates the AST
 * and returns a new updated environment. *)

(* Since these are indexing expressions, the result of evaluating them is int*)
fun evaliexp e env =
    case e of

        (* iterator or parameter variable read *)
        VarExp id => Tuple1D(getint(envlookup(env, id)))

        (* constant integer value *) 
        | Const x => Tuple1D(x) 

        (* index array read, e.g., f(i) *)
        | ISub(id,e) => isub( getivec(envlookup(env,id)), (evaliexp e env) )

(* FIXME: right now returns a real, later should return DValue? *)
fun evaldexp de env =
    case de of
        Convert (e) => let val Tuple1D(i) = evaliexp e env 
                         in Real.fromInt(i) end
      | Read (id,e) => dsub(getrealvec(envlookup(env,id)),(evaliexp e env))
      | DValue(v) => v

(* Result of interpreting exprs is a value. *)
(*
fun evalexpr e env =
    case e of 
         VarExp id => (*FIXME: need to change env to have all "value"s *)
       | ISub of string * expr
       | Opn of (value list -> value ) (expr list)
       | Value v => v
*)

fun evalstmt ast env =
    case ast of
        (* Looks up current value of data array and iterator and then updates
         * a location in the data array based on write function, reads,
         * and the value function that computes the rhs of define stmt.
         *)
        AssignStmt (Aname,wf,reads,vf) =>
        let
            val rhs = vf (map (fn read => evaldexp read env) reads) 
            val Aval = getrealvec(envlookup (env, Aname))
        in
            envupdate(env, Aname, 
                      RealVecVal(dupdate(Aval, (evaliexp wf env), rhs)))
        end

      (* Allocate and initialize an int vector in environment. *)
      (* FIXME: need to let initval type drive what is put in env? *)
      | Malloc (Aname, indom, outdom, initval) =>
        envupdate( env, Aname, IVecVal( empty_iv(indom,outdom,initval) ) )

      (* Right now the interpretation of ForLoop assumes domain1D
       * and therefore only one iterator. *)
      | ForLoop (itername::[],dom,bodyast) =>
        FOR dom
            (fn Tuple1D(iterval) => fn env =>
                let 
                    val env = envupdate(env, itername, IntVal(iterval))
                in 
                    evalstmt bodyast env
                end)
            env

      (* Right now the interpretation of ForLoop assumes lb=0. *)
      (* FIXME: need some way of doing random ordering of evaluations to
       * model concurrency. *)
      | ParForLoop (itername::[],dom,bodyast) =>
        FOR dom
            (fn Tuple1D(iterval) => fn env =>
                let 
                    val env = envupdate(env, itername, IntVal(iterval))
                in 
                    evalstmt bodyast env
                end)
            env

      | SeqStmt (stmts) =>
        foldl (fn (stm,env) => evalstmt stm env) env stmts


