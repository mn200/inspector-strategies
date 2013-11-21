(* inspector primitives
 *
 *)
 
signature primitives =
sig
  
  type mvector
  type mrelation


(* Hiding implementation details in the interface declaration.  
  type mvector = (int -> int) * int
  type mrelation = ((int * int -> bool) * int * int)
*)

  (* Create an empty vector domain [0,0) *)
  val empty_v : mvector

  (* return a vector where given index has been changed to given value *)
  val update : mvector * int * int -> mvector

  (* create a relation with the specified domain [0,N)x[0,M) *)
  val empty_r : int * int -> mrelation

  (* created relation should include old relation union new pair *)
  val r_update : mrelation * int * int -> mrelation

  val sub : mvector * int -> int
  val rsub : mrelation * int * int -> bool

  val size : mvector -> int
  val rsizex : mrelation -> int
  val rsizey : mrelation -> int

  val list_to_mvector : int list -> mvector
  val mvector_to_list : mvector -> int list
  val list_to_mrel : (int*int) -> (int * int) list -> mrelation
  val mrel_to_list : mrelation -> (int * int) list
  val mrel_at_x : mrelation -> int -> int list
  val mrel_at_y : mrelation -> int -> int list

(*
         val C,D,f,g :  mvector
         val E :  mrelation

  val f = list_to_mvector [1,2,3,4]

*)

  datatype direction = X | Y

  (* RFOR dir f mrel acc
     
     is a functional for loop over the (x,y) relations in mrel.
     dir indicates whether to visit the relations in order of X or Y
     values.  f is the body of the loop and modifies the accumulator.
  *)
  val RFOR : direction -> ((int * int) -> 'a -> 'a) -> mrelation -> 'a -> 'a
 

  val FOR : (int * int) -> (int -> 'a -> 'a) -> 'a -> 'a
  (* FOR (lo, hi) f acc

     is a functional for-loop that iterates over indices lo to hi
     (i.e., for (i=lo; i<hi; i++)), and transforms the "state", which
     is the polymorphic 'a above.  The body of the loop implements the
     transformation and gets access to the index and to the current state.
     It's responsibility is to calculate the value of the state for the
     next iteration.
  *)
end
