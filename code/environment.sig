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

    (* function for modifying value associated with a string *)
    val envupdate : envtype * string * valuetype -> envtype

end
