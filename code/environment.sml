(* environment implementation
 *
 * Includes a dictionary implementation.
 *)

use "primitives.sig";
use "primitives.sml";

use "environment.sig"; (* FIXME: why needed? *)

open primitives


structure environment :> environment =
struct

  exception VarNotFound of string

  (**** Dictionary implementation ****)
  type 'a dict = string -> 'a option

  (* I think the insert works like an update as well *)
  fun insert (key : string, value) d = fn s => if s=key
                                               then SOME value
                                               else d s

  fun lookup key d =
     case (d key) of
         NONE => raise VarNotFound(key)
       | SOME value => value 
                                     
  (*** value union type ***)
  datatype valuetype = RelVal of mrelation
                     | IVecVal of ivector
                     | RealVecVal of real dvector
                     | IntVal of int

  fun getmrel v = case v of RelVal(r) => r
  fun getivec v = case v of IVecVal(iv) => iv
  fun getrealvec v = case v of RealVecVal(dv) => dv
  fun getint v = case v of IntVal(i) => i

  (*** env type ***)
  type envtype = valuetype dict
(*
  type envtype = { vdict : int dict,  (* parameter and iterator dict *)
                   ddict : real dvector dict, 
                   idict : ivector dict, 
                   rdict : mrelation dict }
*)
  val empty_env = (fn key => NONE) : envtype

  fun envlookup (env,str) = lookup str env

  fun envupdate (env,str,value) = insert (str,value) env
(*
  fun venvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=insert (str,value) v, ddict=d, idict=i, rdict=r}

  fun denvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=v, ddict=insert (str,value) d, idict=i, rdict=r}

  fun ienvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=v, ddict=d, idict=insert (str,value) i, rdict=r}

  fun renvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=v, ddict=d, idict=i, rdict=insert (str,value) r}
*)
end
