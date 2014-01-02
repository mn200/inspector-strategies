structure primitives :> primitives =
struct

  type 'a dvector = (int -> 'a) * int
  type ivector = (int -> int) * int * int
  type mrelation = ((int * int -> bool) * int * int)

  datatype direction = X | Y

  fun FOR (lo,hi) f acc = if lo >= hi then acc else FOR (lo+1,hi) f (f lo acc)

  (*val empty_v = (fn _ => raise Fail "indexing past end of vector", 0)*)
  fun empty_dv (N, initval) =
      (fn idx => if (0<=idx andalso idx<N) 
		 then initval 
		 else raise Fail "index out of bounds",
       N)

  fun empty_iv (N,M) =
      (fn idx => if (0<=idx andalso idx<N) 
		 then 0 
		 else raise Fail "index out of bounds",
       N, M)

  fun fnsub (f, i, xsz) =
      if (0<=i andalso i < xsz) then f i
      else raise Fail "indexing out of bounds"

  fun dsub((f,xsz): 'a dvector, i) =
      fnsub (f, i, xsz)

  fun isub((f,xsz,ysz): ivector, i) = 
      fnsub (f, i, xsz)

  fun fnupdate f idx v = (fn x => if x = idx then v else f x)

  fun dupdate ((f,xsz) : 'a dvector, idx, v) =
      (fnupdate f idx v, xsz)
  fun iupdate ((f,xsz,ysz) : ivector, idx, v) =
      (fnupdate f idx v, xsz, ysz)

  fun empty_r (n,m) = ((fn _ => false), n, m)
  fun rsub ((rf,xsz,ysz), x, y) =
      if x < xsz andalso y < ysz then rf(x,y)
      else raise Fail "indexing outside relation's domain"
  fun r_update ((rf, xsz, ysz), x, y) =
      (fnupdate rf (x,y) true, Int.max(xsz,x+1), Int.max(ysz,y+1))

  fun dsizex ((f,xsz) : 'a dvector) = xsz
  fun isizex ((f,xsz,ysz) : ivector) = xsz
  fun isizey ((f,xsz,ysz) : ivector) = ysz
  fun rsizex ((rf,xsz,ysz) : mrelation) = xsz
  fun rsizey ((rf,xsz,ysz) : mrelation) = ysz

  fun list_to_dvector l =
      ((fn i => Vector.sub(Vector.fromList l,i)), length l)

  fun list_to_ivector l =
      let val vec = Vector.fromList l
      in
	  ((fn i => Vector.sub(vec,i)), 
	   length l,
	   (* compute the max value for values, assume 0 is min *)
	   foldl (fn (v,max) => if v>max then v else max)
		 0 
		 l
	  )
      end


  fun dvector_to_list (f, sz) =
      List.rev (FOR (0,sz) (fn i => fn l => f i :: l) [])

  fun ivector_to_list (f, xsz, ysz) =
      List.rev (FOR (0,xsz) (fn i => fn l => f i :: l) [])


  fun list_to_mrel (N,M) = List.foldl (fn ((x,y), r) => r_update (r,x,y))
                                      (empty_r (N,M))

  fun mrel_to_list (mf, xsz, ysz) =
       FOR(0,xsz) (fn x => fn l =>
         FOR (0, ysz)
           (fn y => fn l => if mf (x,y) then (x,y)::l else l)
           l)
           []

  fun RFOR_AT_X f (mf, xsz, ysz) x acc =
      FOR (0,ysz) 
	  (fn y => fn acc => if mf(x,y) then f y acc else acc) 
	  acc

  fun mrel_at_y (mf, xsz, ysz) y =
      List.rev
          (FOR(0,xsz) (fn x => fn l => if mf(x,y) then x::l else l) [])

  fun RFOR dir f mrel acc =
      case dir of
	  X => FOR (0, rsizex(mrel))
		   (fn x => RFOR_AT_X (fn y => f(x,y)) mrel x)
(*
		   (fn x => fn acc =>
		       let val row = mrel_at_x mrel x
		       in
			   foldl (fn(y,acc) => f(x,y) acc) acc row
		       end)
*)
		   acc
	| Y => FOR (0,rsizey(mrel))
                   (fn y => fn acc => 
		       let val col = mrel_at_y mrel y
		       in
			   foldl (fn(x,acc) => f(x,y) acc) acc col
		       end)
		   acc


end

