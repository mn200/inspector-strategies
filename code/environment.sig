(* Interface for the environment while interpreting inspectors and executors.
 *)

use "primitives.sig";
open primitives

signature environment =
sig
    type envtype
    type valuetype

    val RelVal : mrelation -> valuetype
    val IVecVal : ivector -> valuetype
    val RealVecVal : real dvector -> valuetype
    val IntVal : int -> valuetype

    val getmrel : valuetype -> mrelation
    val getivec : valuetype -> ivector
    val getrealvec : valuetype -> real dvector
    val getint : valuetype -> int

    exception VarNotFound of string

    (* constructor *)
    val empty_env : envtype

    (* function for looking up a value associated with a string *)
    val envlookup : envtype * string -> valuetype
(*
    val vlookup : envtype * string -> int

    val dlookup : envtype * string -> real dvector
    
    val ilookup : envtype * string -> ivector

    val rlookup : envtype * string -> mrelation
*)
    (* function for modifying value associated with a string *)
    val envupdate : envtype * string * valuetype -> envtype

(*
    val venvupdate : envtype * string * int -> envtype

    val denvupdate : envtype * string * real dvector -> envtype

    val ienvupdate : envtype * string * ivector -> envtype

    val renvupdate : envtype * string * mrelation -> envtype
*)
end
