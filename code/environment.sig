(* Interface for the environment while interpreting inspectors and executors.
 *)

use "primitives.sig";
open primitives

signature environment =
sig
    type envtype

    (* constructor *)
    val empty_env : envtype

    (* functions for looking up each of the value types *)
    val dlookup : envtype * string -> real dvector option
    
    val ilookup : envtype * string -> ivector option

    val rlookup : envtype * string -> mrelation option

    (* functions for modifying value associated with a string *)
(*    val denvupdate : envtype -> string -> 'a dvector -> envtype

    val ienvupdate : envtype -> string -> ivector -> envtype

    val renvupdate : envtype -> string -> mrelation -> envtype
*)
end
