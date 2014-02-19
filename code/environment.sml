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

  (**** Dictionary implementation ****)
  type 'a dict = string -> 'a option

  val empty_dict : 'a dict = fn key => NONE

  fun insert (key, value) d = fn s => if s=key
                                    then SOME value
                                    else d s

  fun lookup key d = d key

  (*** env type ***)
  type envtype = { ddict : real dvector dict, 
                   idict : ivector dict, 
                   rdict : mrelation dict }

  val empty_env = { ddict = fn key => NONE,
                    idict = fn key => NONE,
                    rdict = fn key => NONE} : envtype

  (*** functions to access environment ***)
  fun dlookup ({ddict=d, idict=i, rdict=r}, str) = lookup str d

  fun ilookup ({ddict=d, idict=i, rdict=r}, str) = lookup str i

  fun rlookup ({ddict=d, idict=i, rdict=r}, str) = lookup str r

  (*** functions to modify environment ***)
(*  fun denvupdate {ddict=d, idict=i, rdict=r} str dv =
  *)    

end
