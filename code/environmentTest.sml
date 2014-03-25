(* Testing code for environment implementations *)
use "environment.sml";
open environment

val env = empty_env

(* Michael: equality type required? *)
(*
val env_test1 = dlookup (env,"hi") = NONE : real dvector option
*)
val env_test1 = (envlookup (env,"hi"))
                handle 
                VarNotFound var =>
                (print ("Var not found: " ^ var ^ "\n"); IntVal(0))

val env_test2 = envlookup (env, "bye")
                handle 
                VarNotFound var =>
                (print ("Var not found: " ^ var ^ "\n"); IntVal(0))


val env_test3 = envlookup (env, "there")
                handle 
                VarNotFound var =>
                (print ("Var not found: " ^ var ^ "\n"); IntVal(0))


val env_test4 = envlookup (envupdate (env, "hi", (RealVecVal(empty_dv(5, 0.0)))), "hi")
