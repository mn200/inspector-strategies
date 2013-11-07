structure primitives :> primitives =
struct

  type mvector = (int -> int) * int
  type mrelation = ((int * int -> bool) * int * int)

  fun FOR (lo,hi) f acc = if lo >= hi then acc else FOR (lo+1,hi) f (f lo acc)

  fun fnupdate f d r = (fn x => if x = d then r else f x)
  val empty_v = (fn _ => raise Fail "indexing past end of vector", 0)
  fun sub((f,sz): mvector, i) = if i < sz then f i
                                else raise Fail "indexing past end of vector"
  fun update ((f,sz) : mvector, i, v) =
      (fnupdate f i v, Int.max(sz,i+1))

  val empty_r = ((fn _ => false), 0, 0)
  fun rsub ((rf,xsz,ysz), x, y) =
      if x < xsz andalso y < ysz then rf(x,y)
      else raise Fail "indexing outside relation's domain"
  fun r_update ((rf, xsz, ysz), x, y) =
      (fnupdate rf (x,y) true, Int.max(xsz,x+1), Int.max(ysz,y+1))

  fun list_to_mvector l =
      ((fn i => Vector.sub(Vector.fromList l,i)), length l)
  fun mvector_to_list (f, sz) =
      List.rev (FOR (0,sz) (fn i => fn l => f i :: l) [])


    val list_to_mrel = List.foldl (fn ((x,y), r) => r_update (r,x,y))
                                  empty_r
    fun mrel_to_list (mf, xsz, ysz) =
       FOR(0,xsz) (fn x => fn l =>
         FOR (0, ysz)
           (fn y => fn l => if mf (x,y) then (x,y)::l else l)
           l)
           []

    fun mrel_at_x (mf, xsz, ysz) x =
      List.rev
          (FOR(0,ysz) (fn y => fn l => if mf(x,y) then y::l else l) [])




end
