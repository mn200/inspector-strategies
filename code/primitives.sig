(* inspector primitives
 *
 *)
 
signature primitives =
sig
  
  type 'a dvector (* data array *)
  type ivector    (* index array, or explicit function *)
  type mrelation  (* explicit relation *)

  (* descriptor for a set of integer tuples *)
  datatype domain = Domain1D of int*int    (* [lb,ub) *)

  (* integer tuple *)
  datatype tuple = Tuple1D of int

  (* check if given integer tuple is within a domain *)
  val in_domain : tuple * domain -> bool

  (* return the number of integer tuples in given domain *)
  val size_domain : domain -> int

  (* Create a data vector with index domain and given initial values. *)
  val empty_dv : domain * 'a -> 'a dvector

  (* Create a vector with given index/input domain and range and
   * an initial value for all entries. *)
  val empty_iv : domain * domain * tuple -> ivector

  (* return a vector where given index has been changed to given value *)
  val dupdate : 'a dvector * tuple * 'a  -> 'a dvector
  val iupdate : ivector * tuple * tuple -> ivector

  (* create a relation with the specified input/X and output/Y domains *)
  val empty_r : domain * domain -> mrelation

  (* created relation should include old relation union new pair *)
  val r_update : mrelation * tuple * tuple -> mrelation

  (* needed conversions, FIXME: might be able to get rid of first one *)
  val intdvector_to_ivector : int dvector * domain -> ivector
  val ivector_to_mrel : ivector -> mrelation

  (* index into vectors or relation *)
  val isub : ivector * tuple -> tuple
  val dsub : 'a dvector * tuple -> 'a
  val rsub : mrelation * tuple * tuple -> bool

  (* Return domain or range *)
  val ddomx : 'a dvector -> domain
  val idomx : ivector -> domain
  val idomy : ivector -> domain
  val rdomx : mrelation -> domain
  val rdomy : mrelation -> domain

  (* utility functions for testing and initialization *)
  (* FIXME: interface would have to change for other than 1D domains *)
  val list_to_dvector : 'a list -> 'a dvector
  val list_to_ivector : int list -> ivector
  val dvector_to_list : 'a dvector -> 'a list
  val ivector_to_list : ivector -> int list
  val list_to_mrel : (domain*domain) -> (int * int) list -> mrelation
  val mrel_to_list : mrelation -> (int * int) list

  datatype direction = X | Y

  (* RFOR dir f mrel acc
     
     is a functional for loop over the (x,y) relations in mrel.
     dir indicates whether to visit the relations in order of X or Y
     values.  f is the body of the loop and modifies the accumulator.
  *)
  val RFOR : direction -> ((tuple * tuple) -> 'a -> 'a) -> mrelation -> 'a -> 'a

 (* RFOR_AT_X f mrel x acc

    is a functional to loop over all y's associated with the given
    x.  f is the body of the loop and modifies the accumulator.
  *) 
  val RFOR_AT_X : (tuple -> 'a -> 'a) -> mrelation -> tuple -> 'a -> 'a 

 (* RFOR_AT_Y f mrel y acc

    is a functional to loop over all x's associated with the given
    y.  f is the body of the loop and modifies the accumulator.
  *) 
  val RFOR_AT_Y : (tuple -> 'a -> 'a) -> mrelation -> tuple -> 'a -> 'a 

  (* FOR dom f acc

     is a functional fo r-loop that iterates over indices in a given domain.
     Currently only implemented for domain1D so will go lo to hi
     (i.e., for (i=lo; i<hi; i++)), and transforms the "state", which
     is the polymorphic 'a above.  The body of the loop implements the
     transformation and gets access to the index and to the current state.
     It's responsibility is to calculate the value of the state for the
     next iteration.
     
     Specific to tuple1D right now.
  *)
  val FOR : domain -> (tuple -> 'a -> 'a) -> 'a -> 'a

  (* debugging routines *)
  val dump_dvector : int dvector -> string -> int
end
