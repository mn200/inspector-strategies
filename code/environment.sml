(* environment implementation
 *
 * Includes a dictionary implementation.
 *)

use "primitives.sig";
use "primitives.sml";

use "environment.sig"; (* why needed? *)

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
                                     

  (*** env type ***)
  type envtype = { vdict : int dict,  (* parameter and iterator dict *)
                   ddict : real dvector dict, 
                   idict : ivector dict, 
                   rdict : mrelation dict }

  val empty_env = { vdict = fn key => NONE,
                    ddict = fn key => NONE,
                    idict = fn key => NONE,
                    rdict = fn key => NONE} : envtype

  (*** functions to access environment ***)
  fun vlookup ({vdict=v, ddict=d, idict=i, rdict=r}, str) =
      lookup str v

  fun dlookup ({vdict=v, ddict=d, idict=i, rdict=r}, str) = 
      lookup str d

  fun ilookup ({vdict=v, ddict=d, idict=i, rdict=r}, str) = 
      lookup str i

  fun rlookup ({vdict=v, ddict=d, idict=i, rdict=r}, str) = 
      lookup str r

  (*** functions to modify environment ***)
  fun venvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=insert (str,value) v, ddict=d, idict=i, rdict=r}

  fun denvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=v, ddict=insert (str,value) d, idict=i, rdict=r}

  fun ienvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=v, ddict=d, idict=insert (str,value) i, rdict=r}

  fun renvupdate ({vdict=v, ddict=d, idict=i, rdict=r}, str, value) =
      {vdict=v, ddict=d, idict=i, rdict=insert (str,value) r}

end
