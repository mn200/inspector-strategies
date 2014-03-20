(* Interface for the environment while interpreting inspectors and executors.
 *)

use "primitives.sig";
open primitives

signature environment =
sig
    type envtype

    exception VarNotFound of string

    (* constructor *)
    val empty_env : envtype

    (* functions for looking up each of the value types *)
    val vlookup : envtype * string -> int

    val dlookup : envtype * string -> real dvector
    
    val ilookup : envtype * string -> ivector

    val rlookup : envtype * string -> mrelation

    (* functions for modifying value associated with a string *)
    val venvupdate : envtype * string * int -> envtype

    val denvupdate : envtype * string * real dvector -> envtype

    val ienvupdate : envtype * string * ivector -> envtype

    val renvupdate : envtype * string * mrelation -> envtype

end
