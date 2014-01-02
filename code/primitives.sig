(* inspector primitives
 *
 *)
 
signature primitives =
sig
  
  type 'a dvector (* data array *)
  type ivector    (* index array, or explicit function *)
  type mrelation  (* explicit relation *)

  (* Create a data vector with domain [0,N) and given initial values. *)
  val empty_dv : int * 'a -> 'a dvector

  (* Create a vector with domain [0,N) and range [0,M) and
   * set all initial values to 0. *)
  val empty_iv : int * int -> ivector

  (* return a vector where given index has been changed to given value *)
  val dupdate : 'a dvector * int * 'a  -> 'a dvector
  val iupdate : ivector * int * int -> ivector

  (* create a relation with the specified domain [0,N)x[0,M) *)
  val empty_r : int * int -> mrelation

  (* created relation should include old relation union new pair *)
  val r_update : mrelation * int * int -> mrelation

  (* index into vectors or relation *)
  val isub : ivector * int -> int
  val dsub : 'a dvector * int -> 'a
  val rsub : mrelation * int * int -> bool

  (* Return domain size (x) or range size (y) *)
  val dsizex : 'a dvector -> int
  val isizex : ivector -> int
  val isizey : ivector -> int
  val rsizex : mrelation -> int
  val rsizey : mrelation -> int

  (* utility functions for testing and initialization *)
  val list_to_dvector : 'a list -> 'a dvector
  val list_to_ivector : int list -> ivector
  val dvector_to_list : 'a dvector -> 'a list
  val ivector_to_list : ivector -> int list
  val list_to_mrel : (int*int) -> (int * int) list -> mrelation
  val mrel_to_list : mrelation -> (int * int) list
(*  val mrel_at_y : mrelation -> int -> int list *)


  datatype direction = X | Y

  (* RFOR dir f mrel acc
     
     is a functional for loop over the (x,y) relations in mrel.
     dir indicates whether to visit the relations in order of X or Y
     values.  f is the body of the loop and modifies the accumulator.
  *)
  val RFOR : direction -> ((int * int) -> 'a -> 'a) -> mrelation -> 'a -> 'a

 (* RFOR_AT_X f mrel x acc

    is a functional to loop over all y's associated with the given
    x.  f is the body of the loop and modifies the accumulator.
  *) 
  val RFOR_AT_X : (int -> 'a -> 'a) -> mrelation -> int -> 'a -> 'a 

  (* FOR (lo, hi) f acc

     is a functional fo r-loop that iterates over indices lo to hi
     (i.e., for (i=lo; i<hi; i++)), and transforms the "state", which
     is the polymorphic 'a above.  The body of the loop implements the
     transformation and gets access to the index and to the current state.
     It's responsibility is to calculate the value of the state for the
     next iteration.
  *)
  val FOR : (int * int) -> (int -> 'a -> 'a) -> 'a -> 'a
end
