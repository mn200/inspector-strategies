(* Testing code for environment implementations *)
use "environment.sml";
open environment

val env = empty_env

(* Michael: equality type required? *)
(*
val env_test1 = dlookup (env,"hi") = NONE : real dvector option
*)
val env_test1 = dlookup (env,"hi")

val env_test2 = ilookup (env, "bye")

val env_test3 = rlookup (env, "there")

val env_test4 = dlookup (denvupdate (env, "hi", (empty_dv(5, 0.0))), "hi")
