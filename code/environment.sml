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
  type envtype = { iterdict : int dict,
                   ddict : real dvector dict, 
                   idict : ivector dict, 
                   rdict : mrelation dict }

  val empty_env = { iterdict = fn key => NONE,
                    ddict = fn key => NONE,
                    idict = fn key => NONE,
                    rdict = fn key => NONE} : envtype

  (*** functions to access environment ***)
  fun iterlookup ({iterdict=iter, ddict=d, idict=i, rdict=r}, str) =
      lookup str iter

  fun dlookup ({iterdict=iter, ddict=d, idict=i, rdict=r}, str) = 
      lookup str d

  fun ilookup ({iterdict=iter, ddict=d, idict=i, rdict=r}, str) = 
      lookup str i

  fun rlookup ({iterdict=iter, ddict=d, idict=i, rdict=r}, str) = 
      lookup str r

  (*** functions to modify environment ***)
  fun iterenvupdate ({iterdict=iter, ddict=d, idict=i, rdict=r}, str, value) =
      {iterdict=insert (str,value) iter, ddict=d, idict=i, rdict=r}

  fun denvupdate ({iterdict=iter, ddict=d, idict=i, rdict=r}, str, value) =
      {iterdict=iter, ddict=insert (str,value) d, idict=i, rdict=r}

  fun ienvupdate ({iterdict=iter, ddict=d, idict=i, rdict=r}, str, value) =
      {iterdict=iter, ddict=d, idict=insert (str,value) i, rdict=r}

  fun renvupdate ({iterdict=iter, ddict=d, idict=i, rdict=r}, str, value) =
      {iterdict=iter, ddict=d, idict=i, rdict=insert (str,value) r}

end
