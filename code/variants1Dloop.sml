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

(* dump routines for debugging *)
fun dump_dvector v vstr =
    FOR (0,dsizex(v))
        (fn i => fn count =>
            (print(vstr^"["^Int.toString(i)^"]="^Int.toString(dsub(v,i))^"\n"); dsub(v,i)))
        0

(* when dvector has a boolean value, ick *)
fun dump_bvector v vstr =
    FOR (0,dsizex(v))
        (fn i => fn count =>
            (print(vstr^"["^Int.toString(i)^"]="^Bool.toString(dsub(v,i))^"\n"); dsub(v,i)))
        false


fun dump_ivector v vstr =
    FOR (0,isizex(v))
        (fn i => fn count =>
            (print(vstr^"["^Int.toString(i)^"]="^Int.toString(isub(v,i))^"\n"); isub(v,i)))
        0


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
 * Transformed code in C, use dependence relation directly 
 * and do a topological sort
 *
 * Transformation specification
 *     T = { [i] -> [j] | j=d(i) } is transformation specification
 *
 * User-defined inspector topsort
 *     Assume dinv is inverse of d and that topological sort is returning dinv.
 *
 * Below there are two versions: BFS based one and pack wavefronts.  They 
 * both work.  I uncommented the one that is shortest.
 *)
fun topological_inspector(deps) =
(*
    let
        (* determine number of predecessors in deps graph for each iteration *)
        val num_preds =
            RFOR X
                 (fn (x,y) => fn num_preds =>
                     dupdate(num_preds,y,dsub(num_preds,y)+1))
                 deps
                 (empty_dv(rsizey(deps),0))

        (* find those iterations with no predecessor and put them in queue *)
        val queue =
            FOR (0,dsizex(num_preds))
                (fn y => fn queue =>
                    if dsub(num_preds,y)=0
                    then y::queue
                    else queue)
                []

        (* pack items in the queue into dinv with BFS on deps *)
        fun BFS (queue,num_preds,dinv,visited,count) =
            case queue of
                []    => dinv
             |  x::xs => 
                let
                    (* determine which of x's successors in deps are ready
                     * and decrement their predecessor count *)
                    val (ready_kids,num_preds) =
                        foldl (fn (y,(ready_kids,num_preds)) =>
                                  let val num_preds =
                                          dupdate(num_preds,y,dsub(num_preds,y)-1)
                                  in
                                      if dsub(num_preds,y)=0 
                                         andalso not (dsub(visited,y))
                                      then (y::ready_kids,num_preds)
                                      else (ready_kids,num_preds)
                                  end)
                              ([],num_preds)
                              (mrel_at_x deps x)
                in
                    (* packing x into dinv and then calling BFS on rest of queue *)
                    (* Assuming that there are no self edges in deps, thus
                     * visited not updated until here *)
                    BFS(xs@ready_kids,num_preds,
                        iupdate(dinv,count,x),
                        dupdate(visited,x,true),
                        count+1)
                end
    in
        BFS ( queue, num_preds, 
              empty_iv(rsizey(deps), rsizey(deps)), (* init dinv *)
              empty_dv(rsizey(deps), false), (* init visited *)
              0 )
    end
*)
    let
        (* find wavefront of iterations that can executed, 
         * reduction so can't pack as we look,
         * could check visited, but have to recheck that in pack_wavefront anyway *)
        fun find_wavefront ( dinv, visited, count ) =
            RFOR X
                 (fn (i1,i2) => fn (ready) =>
                     (* if predecessor not visited then not ready *)
                     dupdate(ready,i2,dsub(visited, i1) andalso dsub(ready,i2)))
                 deps
                 (empty_dv(rsizey(deps),true)) (* initially all ready *)

        (* recursively pack all wavefronts  *)
        fun pack_wavefront ( dinv, visited, count ) =
            if count >= rsizey(deps)
            then dinv
            else
                let val ready = find_wavefront( dinv, visited, count )
                    (* have to check if visited here because can't assume
                     * any (v,i) entries in deps *)
                    val (dinv,visited,count) =
                        FOR (0,dsizex(ready))
                            (fn i => fn (dinv, visited, count ) =>
                                if dsub(ready,i) andalso not (dsub(visited,i))
                                then (iupdate(dinv,count,i),
                                      dupdate(visited,i,true),
                                      count+1)
                                else (dinv,visited,count))
                            (dinv,visited,count)
                in
                    pack_wavefront( dinv, visited, count )
                end

    in
        (* initial dinv, visited, and count *)
        pack_wavefront ( empty_iv(rsizex(deps),rsizex(deps)), 
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
(* Variant 3, Fast topological sort
 * Transformed code in C, use data access relations
 * and do a topological sort.  Really fast from the standpoint that the
 * data dependence relation does not have to be constructed.
 *
 * Transformation specification
 *     T = { [i] -> [j] | j=d(i) } is transformation specification
 *
 * User-defined inspector fast top sort
 *     Assume dinv is inverse of d and that topological sort is returning dinv.
 * 
 * Algorithm Sketch
 *     data structures
 *         wave[i] = wavefront for iteration i, init=(numiters-1)
 *         lw_iter[y] = last iteration to write to this data location
 *         lr_iter[y] = last iteration to read this data location
 *     logic
 *         Visit read and write access relation pairs (i,y) in order of 
 *         iterations i.
 *             For read, either
 *                 i is reading from location already written to in i
 *                     thus can be in same wavefront as wave[i], update lr_iter
 *                 i is reading from location written to by a previous iteration
 *                     thus wave[i] = wave[lw_iter[y]] + 1, update lr_iter
 *             For write, either
 *                 i is writing to a location already read or written to in i
 *                     thus can be in same wavefront as wave[i], update lw_iter[y]
 *                 i is writing to loc read or written by a prev iteration
 *                     thus wave[i]=max(wave[lw_iter[y]]+1,wave[lr_iter[y]]+1)
 *                          lw_iter[y]=i
 *         Then do counting sort on iterations based on wave numbers.
 *)
fun fast_top_inspector(R_A,W_A) =
    (* assuming R_A and W_A have same domains and same ranges *)
    let
        (* wavefront number for iteration i *)
        val wave = empty_dv(rsizex(R_A),rsizex(R_A)-1)

        (*  last iteration to write to this data location *)
        val lw_iter = empty_dv(rsizey(R_A),~1)

        (*  last iteration to read from this data location *)
        val lr_iter = empty_dv(rsizey(R_A),~1)

        (* i is iteration, y is data location *)
        fun handle_read i y (wave,lw_iter,lr_iter) =
            (* i reading loc already written to in i *)
            if dsub(lw_iter,y)=i            
            (* just update lr_iter *)
            then (wave,lw_iter,dupdate(lr_iter,y,i))
            (* wave[i] = wave[lw_iter[y]] + 1 *)
            else (dupdate(wave,i,dsub(wave,dsub(lw_iter,y)+1)),
		  lw_iter,
		  dupdate(lr_iter,y,i))

        (* i is iteration, y is data location *)
        fun handle_write i y (wave,lw_iter,lr_iter) =
            (* i writing loc already read or written to in i *)
            if dsub(lw_iter,y)=i orelse dsub(lr_iter,y)=i         
            (* just update lw_iter *)
            then (wave, dupdate(lw_iter,y,i), lr_iter)
            (*  wave[i]=max(wave[lw_iter[y]]+1,wave[lr_iter[y]]+1) *)
            else 
                let 
                    val write_wave = if dsub(lw_iter,y)>=0
                                     then dsub(wave,dsub(lw_iter,y))
                                     else ~1
                    val read_wave = if dsub(lr_iter,y)>=0
                                    then dsub(wave,dsub(lr_iter,y))
                                    else ~1
                    val w = if (write_wave+1) > (read_wave+1)
                            then (write_wave+1)
                            else (read_wave+1)
                in
                    (dupdate(wave,i,w), dupdate(lw_iter,y,i), lr_iter)
                end

        (* assign wavefront numbers to iterations *)
        fun find_waves (wave,lw_iter,lr_iter) =
            (* NOTE, can't use RFORX, have to visit both R_A and W_A *)
            FOR (0,rsizex(R_A))
                (fn i => fn (wave,lw_iter,lr_iter) =>
		    RFOR_AT_X (handle_write i) W_A i
			      (RFOR_AT_X (handle_read i) R_A i
			                 (wave,lw_iter,lr_iter)))
                (wave,lw_iter,lr_iter)

        (* Compute the wave number for each iteration *)
        val (wave,_,_) = find_waves(wave,lw_iter,lr_iter)

        (* Compute the maximum wave value *)
        val max_wave =
            FOR (0,dsizex(wave))
                (fn w => fn (curr_max) =>
                    if dsub(wave,w)>curr_max 
                    then dsub(wave,w) 
                    else curr_max)
                0

        (* pack all iterations based on their wave number
         * and return dinv, inverse of loop permutation *)
        fun pack_waves_simple ( dinv, wave ) =
            let
		(* change wave to ivector *)
		val iwave = intdvector_to_ivector (wave,max_wave+1)

		(* change wave ivector to an mrel *)
		val rwave = ivector_to_mrel iwave
	   
                (* iterate through relation in order of waves
                 * and pack iterations as we see them into dinv *)
                val (dinv,count) = RFOR Y
					(fn (i,w) => fn (dinv,count) =>
					    (iupdate(dinv,count,i), count+1))
					rwave
					(dinv,0)	 
            in
		dinv
	    end


        fun pack_waves_fast ( dinv, wave ) =
            let
                (* iterate over wave and count how many iters per wave *)
                val wcount =
                    FOR (0,dsizex(wave))
                        (fn i => fn (wcount) =>
                            let val w = dsub(wave,i)
                            in dupdate(wcount,w,dsub(wcount,w)+1)
                            end)
                        (empty_dv (max_wave+1,0))

                (*val debug = dump_dvector wcount "wcount"
                val debug = dump_dvector wave "wave"*)

                (* determine where to start putting iterations for each wave *)
                val wstart =
                    FOR (1,dsizex(wcount))
                        (fn i => fn wstart =>
                            dupdate(wstart,i,
                                    dsub(wstart,i-1)+dsub(wcount,i-1)))
                        (empty_dv (dsizex(wcount),0))

                (*val debug = dump_dvector wstart "wstart"*)

                (* use wavestart and another pass over wave to create dinv *)
                val (dinv,wcount) =
                    FOR (0,dsizex(wave))
                        (fn i => fn (dinv,wstart) =>
                            let val w = dsub(wave,i)
                                val j = dsub(wstart,w)
                            in
                                (iupdate(dinv,j,i), dupdate(wstart,w,j+1))
                            end)
                        (dinv, wstart)

                (*val debug = dump_ivector dinv "dinv"*)
            in
                dinv
            end

    in
(*        pack_waves_fast ( empty_iv(rsizex(R_A),0),    (* init dinv *)
                          wave )                      (* wave number per iter *)
*)
	pack_waves_simple ( empty_iv(rsizex(R_A),0), wave )
    end

(* N is number of iterations, M is size of dataspaces *)
(* Only difference with codevariant2 is that the inspector
 * only uses the read and access relations to do the topological
 * sort by wavefront, or level set.
 *)
fun codevariant3 (A,f,g,h,N,M) =
    let
        val R_A = construct_R_A(N,M,g,h)
        val W_A = construct_W_A(N,M,f)
        val dinv = fast_top_inspector(R_A,W_A)
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
(* Variant 4, Reordering the data
 *
 * Transformation specification
 *     R = { A[x] -> A[y] | y=s(x) } is data transformation specification
 *)

fun reorder_data(A,sinv) =
    FOR (0,dsizex(A))
	(fn x => fn Aprime =>
	    dupdate(Aprime, x, dsub(A, isub(sinv,x))))
	(empty_dv(dsizex(A),dsub(A,0)))

fun data_permute_inspector(R_A,W_A,A) =
    let
	(* constructs relation for how iterations access data,
         *     c2d = {[i]->[x] | (i,x) in R_A \/ (i,x) in W_A} 
         * Would be nice to have a union operation for mrels here *)
	val c2d = RFOR X
		       (fn (i,x) => fn c2d =>
			   r_update(c2d, i, x))
		       R_A
		       (RFOR X
			     (fn (i,x) => fn c2d =>
				 r_update(c2d,i,x))
			     W_A
			     (empty_r(rsizex(R_A),rsizex(W_A))))

	val sinv = cpack_inspector(c2d)

        (* need routine for doing inverse of an ivector *)
        val s = FOR (0,isizex(sinv))
                    (fn i => fn s =>
                        iupdate (s, isub(sinv,i), i))
                    (empty_iv (isizey(sinv),isizex(sinv)))

	val Aprime = reorder_data(A,sinv)

    in
	(Aprime,s)
    end

(* Reorders the given data array back to its original order *)
(* Parameters are the reordered data array and the reordering. *)
(* s is old2new mapping. *)
fun post_computation_inspector (Aprime,s) =
    FOR (0,dsizex(Aprime))
	(fn x => fn A =>
	    dupdate(A,x,dsub(Aprime,isub(s,x))))
	(empty_dv (dsizex(Aprime),dsub(Aprime,0)))

(* N is number of iterations, M is size of dataspaces *)
fun codevariant4 (A,f,g,h,N,M) =
    let
        val R_A = construct_R_A(N,M,g,h)
        val W_A = construct_W_A(N,M,f)
        val (Aprime,s) = data_permute_inspector(R_A,W_A,A)
    
        val Aprime =
            FOR (0,N)
		(fn i => fn Aprime =>
                    dupdate(Aprime, isub(s,isub(f,i)), 
			    dsub(Aprime, isub(s, isub(g,i))) 
                            + dsub(Aprime, isub(s, isub(h,i)))))
		Aprime

	(* results provided in the original A order *)
	val A = post_computation_inspector(Aprime,s)

    in
        A
    end


(******************************************************************************)
(******************************************************************************)
(***** Testing for the original loop with deps and all of the variants *****)
(* Original Code in C for loop with deps
 *
 *   for (i=0; i<N; i++) {
 *     A[ f[i] ] =  A[ g[i] ] + A[ h[i] ];
 *   }
 *)

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

(* testing the topological inspectors *)
val top_test1 = 
    ivector_to_list(topological_inspector(construct_Deps(N,R_A2,W_A2)))
    = [0,1,2,3,4]

val fast_top_test1 =
    ivector_to_list(fast_top_inspector(R_A2,W_A2))
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
    (*= [0,3,1,4,2]*)

val fast_top_test2 =
    ivector_to_list(fast_top_inspector(R_A2,W_A2))
    = [0,3,1,4,2]

val variant2_out = dvector_to_list(codevariant2(A,f,g,h,N,M))

val variant2_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant2(A,f,g,h,N,M))

val variant3_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant3(A,f,g,h,N,M))

val variant4_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant4(A,f,g,h,N,M))
