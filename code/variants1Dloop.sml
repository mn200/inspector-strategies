(******************************************************************************)
(* variants1Dloop.sml *)
(******************************************************************************)

(* A fully parallelizable 1D loop implemented functionally
 * and variants of it with various inspector strategies.
 *
 * Here we use some examples to test that the variants
 * produce the same value.  Eventual goal is to prove that
 * the variants will produce the same value for any possible
 * input.
 *)
use "primitives.sig";
use "primitives.sml";
open primitives

(******************************************************************************)
(* Some testing for primitives *)
val iupdate_test1 =
    ivector_to_list( iupdate( empty_iv(3,7), 2, 42)) = [0,0,42]

val dupdate_test1 =
    dvector_to_list( dupdate( empty_dv(3,false), 1, true)) = [false,true,false]






(******************************************************************************)
(* Original Code in C
 *
 * for (i=0; i<N; i++) {
 *     B[i] = C[ f[i] ] + C[ g[i] ];
 * }
 *)
fun orgcode (B,C,f,g,N) =
    FOR (0,N)
        (fn i => fn B => dupdate(B, i, dsub(C, isub(f,i)) + dsub(C, isub(g,i))))
        B

(******************************************************************************)
(* Variant 1
 * Transformed code in C, using cpack heuristic to reorder iterations
 *     T = { [i] -> [j] | j=d(i) /\ 0<=i ... } is transformation specification
 *
 * // Inspector creating hypergraph-like (or CSR-like) representation
 * // for input to lexgroup heuristic.  Stores data to computation relation.
 * //    d2c = { [ x ] -> [ i ] | x=f(i) \/ x=g(i) } 
 * // Showing barebones most efficient code so we start thinking about the
 * // semantic gap we will need to bridge.  Sparse code in all its glory!
 * int* d2c_ptr = calloc((M+1),sizeof(int));
 * int* d2c_i   = calloc( N,   sizeof(int));
 * for (i=0; i<N; i++) { // count number of i's per x
 *   d2c_ptr[f[i]]++;
 *   d2c_ptr[g[i]]++;
 * }
 * for (x=1; x<=M; x++) { // set up d2c_ptr
 *   // d2c_ptr[x] currently has number of i's per x
 *   // now do a scan so that when d2c_ptr[x] is
 *   // used to index into d2c_i will start at end of section for one x
 *   // d2c_ptr[M] will have number of pairs in relation
 *   d2c_ptr[x] = d2c_ptr[x] + d2c_ptr[x-1];
 * }
 * for (i=0; i<N; i++) { // fill d2c_i with i values
 *   // subtract 1 because current count is beginning of next group
 *   // or i values we have already inserted for this x
 *   d2c_i[ --d2c_ptr[f[i]] ] = i;
 *   d2c_i[ --d2c_ptr[g[i]] ] = i;
 * }
 * 
 * // cpack heuristic for creating dinv.
 * // dinv = cpack( d2c_ptr, d2c_i, M, N )
 * int* visited = calloc(N,sizeof(int));  // which iterations have been packed
 * int count = 0;
 * for (x=0; x<M; x++) {
 *   for (p=d2c_ptr[x]; p<d2c_ptr[x+1]; p++) {
 *     i = d2c_i[p];
 *     if (!visited[i]) { dinv[count++] = i; visited[i] = 1; }
 *   }
 * }
 * // Will want this for more general version of cpack but for
 * // this particular example not needed since know each iteration
 * // i will show up in the relation.
 * for (i=0; i<N; i++) {  \\ check that everyone got reordered
 *   if (!visited[i]) { dinv[count++] = i; }
 *
 * // transformed executor
 * for (j=0; j<N; j++) {
 *     B[dinv[j]] = C[ f[dinv[j]] ] + C[ g[dinv[j]] ];
 * }
 *)
(* constructs mrel for d2c = { [ x ] -> [ i ] | x=f(i) \/ x=g(i) } *)
(* M is the domain size [0,M). *)
(* N is the range size [0,N) or possible values of i. *)
fun construct_explicit_relation (M,N,f,g) =
    FOR (0,N)
        (fn i => fn E => r_update(r_update(E,isub(f,i),i), isub(g,i),i))
        (empty_r (M,N))


(* Using 0 and 1 for false and true because that is what mvector handles. *)
fun cpack_inspector (E) =
    let 
        val visited = empty_dv ( rsizey(E), false )
        val count = 0

        (* pack y into dinv, count is current count of packed vals *)
        fun pack (dinv,visited,count,y) =
	    if not( dsub(visited,y) )
	    then ( iupdate(dinv,count,y), dupdate(visited, y, true), count+1 )
            else ( dinv, visited, count )

        (* use the relation to pack values of y as seen 
         * with in order x values *)
        val (dinv,visited,count) = 
	    RFOR X 
		 (fn (x,y) => fn (dinv,visited,count) => 
		     pack(dinv,visited,count,y))
                 E
		 (empty_iv(rsizey(E),rsizey(E)), visited, count)

        (* do cleanup on dinv to ensure all y's in relation have 
         * been ordered in dinv *)
	val (dinv,visited,count) =	 
            FOR (0,rsizey(E))
		(fn y => fn (dinv,visited,count) => pack(dinv,visited,count,y))
		(dinv,visited,count)
    in
	dinv
    end

(* N is number of iterations, M is size of dataspaces *)
fun codevariant1 (B,C,f,g,N,M) =
    let
	val E = construct_explicit_relation(M,N,f,g)
	val dinv = cpack_inspector(E)
    in

	FOR (0,N)
            (fn j => fn B => 
                let val i = isub(dinv,j) in
	            dupdate(B, i, dsub(C, isub(f,i)) + dsub(C, isub(g,i)))
                end )
            B
    end

(******************************************************************************)
(******************************************************************************)
(***** Testing for the original loop with no deps and all of the variants *****)
(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val f = list_to_ivector [1,2,3,4,0]

val g = list_to_ivector [4,3,2,1,0]

val C = list_to_dvector [10,20,30,40,50]
(*
val test_org = dvector_to_list(orgcode (empty_dv(isizex(f),0),C,f,g,5)) 
	       = [70,70,70,70,20]

val er_test1 = mrel_to_list(construct_explicit_relation(5,5,f,g))
*)
val inspec_test1 = 
    ivector_to_list(cpack_inspector( 
			 construct_explicit_relation(5,5,f,g)))
    = [4,0,3,1,2]
(*
val variant1_out = dvector_to_list(
	codevariant1(empty_dv(isizex(f),0),C,f,g,5,5))
*)
val variant1_test1 = dvector_to_list(orgcode(empty_dv(isizex(f),0),C,f,g,5)) 
                     = dvector_to_list(
			 codevariant1(empty_dv(isizex(f),0),C,f,g,5,5))

(* Test where packing needs to do a cleanup pass *)
(* Well no because output of original code doesn't depend on index 2
 * if it just isn't there *)
val f = list_to_ivector [1,1,3,3,0]

val g = list_to_ivector [4,4,1,1,0]

val C = list_to_dvector [10,20,30,40,50]

val variant1_test2 = dvector_to_list(orgcode(empty_dv(isizex(f),0),C,f,g,5)) 
                     = dvector_to_list(
			 codevariant1(empty_dv(isizex(f),0),C,f,g,5,5))

(* What about the output from the inspector? *)
val inspec_test2 = 
    ivector_to_list(cpack_inspector( 
			 construct_explicit_relation(5,5,f,g)))
    = [4,0,1,2,3]

(* Test 3: Another example.  Now N=3 and M=5.  C can stay the same. *)
val fsz3 =  list_to_ivector [0,4,3]
val gsz3 =  list_to_ivector [1,4,2]
(*
val er_test3 = 
    mrel_to_list ( construct_explicit_relation(5,3,fsz3,gsz3) )
    =  [(4,1),(3,2),(2,2),(1,0),(0,0)]
*)
(* Used for debugging. *)
(*val E = construct_explicit_relation(5,3,fsz3,gsz3);
val xsize = rsizex(E);
val ysize = rsizey(E);
val inspec_test3 = 
    ivector_to_list(cpack_inspector(construct_explicit_relation(5,3,fsz3,gsz3)))
*)
val variant1_test3 = dvector_to_list(
	                 orgcode(empty_dv(isizex(fsz3),0),C,fsz3,gsz3,3)) 
		     = dvector_to_list(
			 codevariant1(empty_dv(isizex(fsz3),0),C,fsz3,gsz3,3,5))



(******************************************************************************)
(* Original Code in C for loop with deps
 *
 *   for (i=0; i<N; i++) {
 *     A[ f[i] ] =  A[ g[i] ] + A[ h[i] ];
 *   }
 *)
fun orgcode_with_deps (A,f,g,h,N) =
    FOR (0,N)
        (fn i => fn A => dupdate(A, isub(f,i), 
				 dsub(A, isub(g,i)) + dsub(A, isub(h,i))))
        A

(*
 * Domains and Ranges
 *   Domain for A is [0,M)
 *   Domain for original loop is [0,N)
 *   Domain for f, g, and h is [0,N)
 *   Range for f, g, and h is [0,M)
 *
 * Read Access Relation for A dataspace
 *
 *   R_A = { [i] -> [x] : i in Domain(loop) /\ x in Domain(A) /\
 *                        (x=g(i) \/ x=h(i)) }
 *
 * Write Access Relation for A dataspace
 *
 *   W_A = { [i] -> [x] : i in Domain(loop) /\ x in Domain(A) /\
 *                        x=f(i) }
 *
 * Dependence Relation
 * 
 *   Dep = { [i1] -> [i2] : i1 in Domain(loop) /\ i2 in Domain(loop) /\ 
 *                          i1<i2 /\
 *                          (exists x: ( (i1,x) in R_A /\ (i2,x) in W_A )
 *                                  \/ ( (i1,x) in W_A /\ (i2,x) in W_A )
 *                                  \/ ( (i1,x) in W_A /\ (i2,x) in R_A ) ) }
 *)

(* construct_R_A creates the read access relation for A *)
fun construct_R_A(N,M,g,h) = 
    FOR (0,N)
	(fn i => fn E => r_update(r_update(E,i,isub(g,i)), i, isub(h,i)))
        (empty_r (N,M))

(* construct_W_A creates the write access relation for A *)
fun construct_W_A(N,M,f) = 
    FOR (0,N)
	(fn i => fn E => r_update(E,i,isub(f,i)))
        (empty_r (N,M))

(* construct_Deps creates Deps.*)
fun construct_Deps (N,R_A,W_A) =
    (* finds (i1,i2) st i1<i2 and (i1,y) in rel1 and (i2,y) in rel2 *)
    (* puts those pairs into acc relation and returns it *)
    let fun join_idx(rel1,rel2,acc) =
	    RFOR X
		 (fn (i1,y1) => fn (Deps) =>
		     RFOR X
			  (fn (i2,y2) => fn (Deps) =>
			      if (i1<i2 andalso y1=y2) 
			      then r_update(Deps, i1,i2)
			      else Deps )
			  rel2
			  Deps)
		 rel1
		 acc
    in
	join_idx(W_A,W_A,join_idx(W_A,R_A,join_idx(R_A,W_A,empty_r(N,N))))
    end

(******************************************************************************)
(* Variant 2, Topological sort
 * Transformed code in C, use dependence relation direction 
 * and do a topological sort
 *
 * Transformation specification
 *     T = { [i] -> [j] | j=d(i) } is transformation specification
 *
 * User-defined inspector topsort
 *     Assume dinv is inverse of d and that topological sort is returning dinv.
 *   
 *)
fun topological_inspector(deps) =
    let
        (* find wavefront of iterations that can execute *)
        fun wavefront ( visited, deps ) =
	    RFOR X
                 (* remove iterations where deps not satisfied yet *)
		 (fn (i1,i2) => fn (ready) =>
		     if dsub(visited, i1) = false
		     then dupdate(ready, i2, false)
		     else ready)
		 deps
                 (* start out assuming all iterations are ready *)
		 (empty_dv ( rsizex(deps), true ) )

	(* pack all iterations in wavefront, modifies visited *)
	fun pack_wavefront ( dinv, visited, count, ready ) =
	    FOR (0,dsizex(ready))
		(fn i => fn (dinv, visited, count ) =>
		    if not( dsub(visited,i) ) andalso dsub(ready,i)
		    then (iupdate(dinv,count,i),dupdate(visited,i,true),count+1)
		    else (dinv,visited,count))
		(dinv,visited,count)

	(* returns true if all iterations have been visited *)
	fun all_visited ( visited ) =
	    FOR (0,dsizex(visited))
		(fn i => fn acc => if dsub(visited,i) then acc else false)
		true

        (* recursively pack all wavefronts *)
	fun pack_levels ( dinv, visited, count ) =
	    if all_visited( visited )
	    then dinv
	    else pack_levels(
		    pack_wavefront(dinv,visited,count,wavefront(visited,deps)))
    in
        (* initial dinv, visited, and count *)
	pack_levels ( empty_iv(rsizex(deps),rsizex(deps)), 
		      empty_dv(rsizex(deps),false), 
		      0 )
    end

(* N is number of iterations, M is size of dataspaces *)
fun codevariant2 (A,f,g,h,N,M) =
    let
	val deps = construct_Deps(N,construct_R_A(N,M,g,h),construct_W_A(N,M,f))
	val dinv = topological_inspector(deps)
    in

	FOR (0,N)
            (fn j => fn A => 
                let val i = isub(dinv,j) in
		    dupdate(A, isub(f,i), 
			    dsub(A, isub(g,i)) + dsub(A, isub(h,i)))
                end )
            A
    end



(******************************************************************************)
(******************************************************************************)
(***** Testing for the original loop with no deps and all of the variants *****)
(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val N = 5
val M = 5
val f = list_to_ivector [1,2,1,4,0] (* writes *)
val g = list_to_ivector [4,3,2,1,0] (* reads *)
val h = list_to_ivector [0,1,2,3,4] (* reads *)
(* Deps should have
 *      anti: (0,3),(0,4),(1,2)
 *      flow: (0,1),(1,2),(2,3),(3,4),(0,3)
 *      output: (0,2)
 *)
val R_A = construct_R_A(N,M,g,h)
val test_R_A = mrel_to_list( R_A )
val W_A = construct_W_A(N,M,f)
val test_W_A = mrel_to_list( W_A )
val test_Deps = mrel_to_list(construct_Deps(N,R_A,W_A))

(* Of course above example results in a full order. *)
(* Here is an example that doesn't. *)
val f = list_to_ivector [1,2,1,2,1] (* writes *)
val g = list_to_ivector [4,3,4,3,4] (* reads *)
val h = list_to_ivector [0,3,0,3,0] (* reads *)
val R_A2 = construct_R_A(N,M,g,h)
val test_R_A2 = mrel_to_list( R_A2 )
val W_A2 = construct_W_A(N,M,f)
val test_W_A2 = mrel_to_list( W_A2 )
val test_Deps2 = mrel_to_list(construct_Deps(N,R_A2,W_A2))

(* Now let's do the actual computation *)
val A = list_to_dvector [10,20,30,40,50]
val test_org_with_deps = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
	       = [10,60,80,40,50]

(* testing the topological inspector *)
val top_test1 = 
    ivector_to_list(topological_inspector(construct_Deps(N,R_A2,W_A2)))
    = [0,1,2,3,4]

(* above example results in permutation equal to original order *)
(* here is another example where should get 0,3,1,4,2 *)
val f = list_to_ivector [1,1,1,2,2] (* writes *)
val g = list_to_ivector [4,3,4,3,4] (* reads *)
val h = list_to_ivector [0,3,0,3,0] (* reads *)
val R_A2 = construct_R_A(N,M,g,h)
val test_R_A2 = mrel_to_list( R_A2 )
val W_A2 = construct_W_A(N,M,f)
val test_W_A2 = mrel_to_list( W_A2 )
val test_Deps2 = mrel_to_list(construct_Deps(N,R_A2,W_A2))

val top_test2 = 
    ivector_to_list(topological_inspector(construct_Deps(N,R_A2,W_A2)))
    = [0,3,1,4,2]

val variant2_out = dvector_to_list(codevariant2(A,f,g,h,N,M))

val variant2_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant2(A,f,g,h,N,M))

