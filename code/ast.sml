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

datatype stmt =
         (* Define statement in a 1D loop *)
         (* write idx function, functions, val compute, array   *)
         (* A[ wf(i) ] = vf( read0(i) ], read1(i) ], ... )      *)
         (* e.g. read#(i)=A[i], read#(i)=A[f[i]], or read#(i)=i *)
         AssignStmt of string * iexp            (* wf           *)
                       * dexp list              (* reads        *)
                       * ((real list) -> real)  (* vf           *)

         (* Aname, num, initval, range *)
         | Malloc of string * int * int * int 

         (* for ( lb <= i < ub ) body *)
         | ForLoop of string * int * int * stmt

         (* iterations of loop can be executed concurrently *)
         (* for ( lb <= i < ub ) body *)
         | ParForLoop of string * int * int * stmt

         (* Statement sequencing *)
         | SeqStmt of stmt list


(**** Interpreter ****)
(* Given the AST and the current environment, evaluates the AST
 * and returns a new updated environment. *)

(* Since these are indexing expressions, the result of evaluating them is int*)
fun evaliexp exp env =
    case exp of

        (* iterator or parameter variable read *)
        VarExp id => getint(envlookup(env, id))

        (* constant integer value *) 
        | Const x => x 

        (* index array read, e.g., f(i) *)
        | ISub(id,e) => isub( getivec(envlookup(env,id)), (evaliexp e env) )

(* FIXME: right now returns a real, later should return DValue? *)
fun evaldexp de env =
    case de of
        Convert (exp) => Real.fromInt(evaliexp exp env)
      | Read (id,exp) => dsub(getrealvec(envlookup(env,id)),(evaliexp exp env))
      | DValue(v) => v 

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
      (* FIXME: need to let initval type drive what is put in env *)
      | Malloc (Aname, num, initval, range) =>
        envupdate( env, Aname,
                   IVecVal( 
                       FOR (0,num)
                           (fn i => fn ivec =>
                               iupdate(ivec,i,initval))
                           (empty_iv(num,range)) ) )

      (* Right now the interpretation of ForLoop assumes lb=0. *)
      | ForLoop (itername,lb,ub,bodyast) =>
        FOR (0,ub)
            (fn iterval => fn env =>
                let 
                    val env = envupdate(env, itername, IntVal(iterval))
                in 
                    evalstmt bodyast env
                end)
            env

      (* Right now the interpretation of ForLoop assumes lb=0. *)
      (* FIXME: need some way of doing random ordering of evaluations to
       * model concurrency. *)
      | ParForLoop (itername,lb,ub,bodyast) =>
        FOR (0,ub)
            (fn iterval => fn env =>
                let 
                    val env = envupdate(env, itername, IntVal(iterval))
                in 
                    evalstmt bodyast env
                end)
            env

      | SeqStmt (stmts) =>
        foldl (fn (stm,env) => evalstmt stm env) env stmts


