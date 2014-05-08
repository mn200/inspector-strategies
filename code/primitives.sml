structure primitives :> primitives =
struct

  datatype domain = Domain1D of int * int
  datatype tuple = Tuple1D of int

  type 'a dvector = (tuple -> 'a) * domain
  type ivector = (tuple -> tuple) * domain * domain
  type mrelation = ((tuple * tuple -> bool) * domain * domain)

  datatype direction = X | Y

  fun in_domain (Tuple1D(i),Domain1D(lb,ub)) =
      lb<=i andalso i<=ub

  fun size_domain (Domain1D(lo,hi)) = hi-lo

  fun FOR (Domain1D(lo,hi)) f acc = 
      if lo >= hi then acc 
      else FOR (Domain1D(lo+1,hi)) f (f (Tuple1D(lo)) acc)

  fun empty_dv (dom, initval) =
      (fn idx => if (in_domain(idx,dom)) 
		 then initval 
		 else raise Fail "index out of bounds",
       dom)

  fun empty_iv (indom,outdom,initval) =
      (fn idx => if (in_domain(idx,indom))
		 then initval
		 else raise Fail "index out of bounds",
       indom,outdom)

  fun ddomx ((f,xdom) : 'a dvector) = xdom
  fun idomx ((f,xdom,ydom) : ivector) = xdom
  fun idomy ((f,xdom,ydom) : ivector) = ydom
  fun rdomx ((rf,xdom,ydom) : mrelation) = xdom
  fun rdomy ((rf,xdom,ydom) : mrelation) = ydom

  fun fnsub (f, i, dom) =
      if (in_domain(i,dom)) then f i
      else raise Fail "indexing out of bounds"

  fun dsub((f,dom): 'a dvector, i) =
      fnsub (f, i, dom)

  fun isub((f,indom,outdom): ivector, i) = 
      fnsub (f, i, indom)

  fun fnupdate f idx v = (fn x => if x = idx then v else f x)

  fun dupdate ((f,dom) : 'a dvector, idx, v) =
      (fnupdate f idx v, dom)
  fun iupdate ((f,indom,outdom) : ivector, idx, v) =
      (fnupdate f idx v, indom, outdom)

  fun empty_r (xdom,ydom) = ((fn _ => false), xdom, ydom)
  fun rsub ((rf,xdom,ydom) : mrelation, x, y) =
      if in_domain(x,xdom) andalso in_domain(y,ydom) then rf(x,y)
      else raise Fail "indexing outside relation's domain"
  fun r_update ((rf, xdom, ydom) : mrelation, x, y) =
      if in_domain(x,xdom) andalso in_domain(y,ydom) then
          (fnupdate rf (x,y) true, xdom, ydom)
      else raise Fail "inserting X,Y pair outside relation's domain"

  (* OLD version: enabled the X and Y domain's for relation to be extended
  fun r_update ((rf, xsz, ysz), x, y) =
      (fnupdate rf (x,y) true, Int.max(xsz,x+1), Int.max(ysz,y+1))
  *)

  fun intdvector_to_ivector (dvec,outdom) =
      FOR (ddomx(dvec))
	  (fn x => fn ivec => iupdate (ivec,x,Tuple1D(dsub(dvec,x))))
	  (empty_iv (ddomx(dvec),outdom,Tuple1D(0)))

  fun ivector_to_mrel ivec =
      FOR (idomx(ivec))
	  (fn x => fn mrel => r_update (mrel,x,isub(ivec,x)))
	  (empty_r (idomx(ivec),idomy(ivec)))

  (* specific to Domain1D *)
  fun list_to_dvector l =
      ((fn Tuple1D(i) => Vector.sub(Vector.fromList l,i)), Domain1D(0,length l))

  (* specific to Domain1D *)
  fun list_to_ivector l =
      let val vec = Vector.fromList l
      in
	  ((fn Tuple1D(i) => Tuple1D(Vector.sub(vec,i))), 
	   Domain1D(0,length l),
	   (* compute the max value for values, assume 0 is min *)
           Domain1D(0,
	            foldl (fn (v,max) => if v>max then v else max)
		          0 
		          l
	           ) )
      end


  fun dvector_to_list (f,dom) =
      List.rev (FOR dom 
                    (fn i => fn l => f(i) :: l) 
                    [])

  (* specific to Domain1D *)
  fun ivector_to_list (f, indom, outdom) =
      List.rev ( FOR indom 
                     (fn x => fn l => let val Tuple1D(y) = f(x)
                                      in y::l end )
                     [] )


  (* specific to Domain1D *)
  fun list_to_mrel (xdom,ydom) = 
      List.foldl (fn ((x,y), r) => r_update (r,Tuple1D(x),Tuple1D(y)))
                 (empty_r (xdom,ydom))

  (* currently specific for Domain1D for X and Y *)
  fun mrel_to_list (mf,xdom,ydom) =
       FOR xdom (fn x => fn l =>
         FOR ydom
           (fn y => fn l => let val Tuple1D(xval) = x
                                val Tuple1D(yval) = y
                            in
                                if mf (x,y) then (xval,yval)::l else l
                            end)
           l)
           []

  (* currently specific for Domain1D for X and Y *)
  fun RFOR_AT_X f (mf,xdom,ydom) x acc =
      FOR ydom (fn y => fn acc => if mf(x,y) then f y acc else acc) acc

  (* currently specific for Domain1D for X and Y *)
  fun RFOR_AT_Y f (mf,xdom,ydom) y acc =
      FOR xdom (fn x => fn acc => if mf(x,y) then f x acc else acc) acc

  (* currently specific for Domain1D for X and Y *)
  fun RFOR dir f mrel acc =
      let val (rf,xdom,ydom) = mrel in
          case dir of
	      X => FOR xdom
		       (fn x => RFOR_AT_X (fn y => f(x,y)) mrel x)
		       acc
	    | Y => FOR ydom
		       (fn y => RFOR_AT_Y (fn x => f(x,y)) mrel y)
		       acc
      end

  (* debugging routines *)

  (* assumes a dvector of ints and prints them, evals to count *)
  fun dump_dvector  (v : int dvector) vstr =
    let val (f,dom) = v in
        FOR dom
            (fn i => fn count =>
                let val j = dsub(v,i)
                    val Tuple1D(ival) = i 
                in
                    (print(vstr^"["^Int.toString(ival)^"]="
                           ^Int.toString(j)^"\n"); count+1 ) 
                end )
            0

    end

end

