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
 *           For read, either
 *             i is reading from location already written to in i
 *               thus can be in same wavefront as wave[i], update lr_iter
 *             i is reading from location written to by a previous iteration
 *               thus wave[i] = wave[lw_iter[y]] + 1, update lr_iter
 *           For write, either
 *             i is writing to a location already read or written to in i
 *               thus can be in same wavefront as wave[i], update lw_iter[y]
 *             i is writing to loc read or written by a prev iteration
 *               thus wave[i]=max(wave[lw_iter[y]]+1,wave[lr_iter[y]]+1)
 *                    lw_iter[y]=i
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

                (* determine where to start putting iterations for each wave *)
                val wstart =
                    FOR (1,dsizex(wcount))
                        (fn i => fn wstart =>
                            dupdate(wstart,i,
                                    dsub(wstart,i-1)+dsub(wcount,i-1)))
                        (empty_dv (dsizex(wcount),0))

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
        (fn x => fn Aprime => dupdate(Aprime, x, dsub(A, isub(sinv,x))))
        (empty_dv(dsizex(A),dsub(A,0)))

fun data_permute_inspector(R_A,W_A,A) =
    let
    (* constructs relation for how iterations access data,
     *     c2d = {[i]->[x] | (i,x) in R_A \/ (i,x) in W_A}
     * Would be nice to have a union operation for mrels here *)
        val c2d = RFOR X
                       (fn (i,x) => fn c2d => r_update(c2d, i, x))
                       R_A
                       (RFOR X
                             (fn (i,x) => fn c2d => r_update(c2d,i,x))
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

(**************************************************************************)
(**************************************************************************)
(* Refactoring numbered variants above into three cases that can be
 * parameterized with different inspector reordering heuristics.
 *
 *    dopar_reord: permuting the iterations in a parallel loop
 *    doacross_reord: permuting the iterations when have loop carried deps
 *    data_reord: reordering the data being accessed by a loop
 *
 * Directly below are the various routines these reorderings can use.
 * At the end are the general routines themselves.
 *)

(* find_waves_fast
 * 
 * Maps iterations to parallel wavefronts but avoids explicitly constructing
 * the dependence relation.
 *
 * Assuming inputs R_A and W_A have same domain and range.
 * Assuming one statement so all reads happen before the single write. 
 *
 * Algorithm Sketch
 *     data structures
 *         wave[i] = wavefront for iteration i, init=(numiters-1)
 *         lw_iter[y] = last iteration to write to this data location
 *         lr_iter[y] = last iteration to read this data location
 *     recurrence equations
 *         wave[i] = max( max_{y st (i,y) in R_A}( wave[lw_iter[y,i]]+1 ),
 *                        max_{y st (i,y) in W_A}( wave[lw_iter[y,i]]+1 ),
 *                        max_{y st (i,y) in W_A}( wave[lr_iter[y,i]]+1 ) )
 *         lw_iter[y,i] = max_{0<j<i}( {j | (j,y) in W_A} ) // scan
 *         lr_iter[y,i] = max_{0<j<i}( {j | (j,y) in R_A} ) // scan
 * 
 * Implementation
 *     Won't be fast if just implement recurrences directly.
 *     Is the below an implementation that could derive by doing
 *     optimizations on the above recurrence equations?
 *
 *     Initialize all wave[i] to 0.
 *     Initialize all last write and last read per data item to -1,
 *         assuming iteration starts at 0, assuming at least one write
 *         per iteration.
 *     Visit iterations i in order.
 *         max_prev_wave = -1
 *         For read y
 *             max_prev_wave = max(max_prev_wave,wave[lw_iter[y]])
 *             lr_iter[y] = max(lr_iter[y],i)
 *         For write y, assuming only one
 *             if read data item in this iteration can still be in same wave.
 *             if lr_iter[y]==i then max_prev_wave = max_prev_wave
 *             else max_prev_wave = max(max_prev_wave,
 *                                      wave[lr_iter[y]],
 *                                      wave[lw_iter[y]])
 *             lw_iter[y] = i
 *         wave[i] = max_prev_wave + 1
 *)
fun find_waves_fast (R_A, W_A) =
    let
        (* wavefront number for iteration i *)
        (* initially all put into wave 0 and range is overapproximated *)
        val wave = empty_iv(rsizex(R_A),rsizex(R_A))

        (*  last iteration to write to this data location *)
        val lw_iter = empty_dv(rsizey(R_A),~1)
        (*  last iteration to read from this data location *)
        val lr_iter = empty_dv(rsizey(R_A),~1)

        (* if indexing wave with -1, then return -1 for value so +1 works *)
        fun wave_val (wave, idx) =
            if idx>=0
            then isub(wave,idx)
            else ~1

        (* i is iteration, y is data location *)
        fun handle_read i y (wave,lw_iter,lr_iter,max_prev_wave) =
            (* lr_iter[y] = max(lr_iter[y],i) *)
            (* max_prev_wave = max(max_prev_wave,wave[lw_iter[y]]) *)
            (wave, lw_iter, dupdate(lr_iter,y,i),
             Int.max(max_prev_wave,wave_val(wave,dsub(lw_iter,y))) )

        (* i is iteration, y is data location *)
        fun handle_write i y (wave,lw_iter,lr_iter:int dvector, max_prev_wave) =
            (* update lw_iter[y] to i *)
            (* if read data item in this iteration can still be in same wave
             * else need to detect prev wave that i depends on *)
            (wave, dupdate(lw_iter,y,i), lr_iter,
             if dsub(lr_iter,y) = i 
             then max_prev_wave
             else Int.max(max_prev_wave,
                          Int.max(wave_val(wave,dsub(lr_iter,y)), 
                                  wave_val(wave,dsub(lw_iter,y)))) )
            
        (* assign wavefront numbers to iterations *)
        val (wave,_,_,_) =
            (* NOTE, can't use RFORX, have to visit both R_A and W_A *)
            FOR (0,rsizex(R_A))
                (fn i => fn (wave,lw_iter,lr_iter,max_prev_wave) =>
                    RFOR_AT_X (handle_write i) W_A i
                              (RFOR_AT_X (handle_read i) R_A i
                                         (wave,lw_iter,lr_iter,max_prev_wave)))
                (* init max_prev_wave to -1 *)
                (wave,lw_iter,lr_iter,~1)

    in
        wave
    end


(* pack_waves_simple
 *
 * Pack all iterations based on their wave number and return dinv,
 * inverse of loop permutation.
 *
 * wave - ivector with mapping of iterations to wave fronts
 *)
fun pack_waves_simple wave =
    let
        (* change wave ivector to an mrel *)
        val rwave = ivector_to_mrel wave
       
        (* iterate through relation in order of waves
         * and pack iterations as we see them into dinv *)
        val (dinv,count) = RFOR Y
                                (fn (i,w) => fn (dinv,count) =>
                                    (iupdate(dinv,count,i), count+1))
                                rwave
                                (empty_iv(isizex(wave),isizey(wave)),0)
    in
        dinv
    end

(* Instead of creating an mrel and iterating over it in Y order,
 * this routine counts up number of iterations in each wave and
 * then sorts them this way.  Basically this is a counting sort. *)
fun pack_waves_fast wave =
    let
        (* iterate over wave and count how many iters per wave *)
        val wcount =
            FOR (0,isizex(wave))
                (fn i => fn (wcount) =>
                    let val w = isub(wave,i)
                    in dupdate(wcount,w,dsub(wcount,w)+1)
                    end)
                (empty_dv (isizey(wave),0))

        (* determine where to start putting iterations for each wave *)
        val wstart =
            FOR (1,dsizex(wcount))
                (fn i => fn wstart =>
                    dupdate(wstart,i,
                            dsub(wstart,i-1)+dsub(wcount,i-1)))
                (empty_dv (dsizex(wcount),0))

        (* use wavestart and another pass over wave to create dinv *)
        val (dinv,wcount) =
            FOR (0,isizex(wave))
                (fn i => fn (dinv,wstart) =>
                    let val w = isub(wave,i)
                        val j = dsub(wstart,w)
                    in
                        (iupdate(dinv,j,i), dupdate(wstart,w,j+1))
                    end)
                (empty_iv(isizex(wave),isizey(wave)), wstart)

    in
        dinv
    end


(* Iteration Reordering, DOACROSS Loop *)
(* Input:
 *     R_A is the read access relation.
 *     W_A is the write access relation.
 *     wavef is a function that maps iterations to parallel wavefronts.
 *     packf is a function that packs iterations based on their wavefront.
 * Output:
 *     dinv maps new iteration order to old iteration order
 *)
fun doacross_reord ( R_A, W_A, wavef, packf ) =
    packf( wavef( R_A, W_A ) )

fun codevariant_doacross_reord (A,f,g,h,N,M, wavef, packf) =
    let
        val R_A = construct_R_A(N,M,g,h)
        val W_A = construct_W_A(N,M,f)
        val dinv = doacross_reord(R_A, W_A, wavef, packf)
    in
        FOR (0,N)
            (fn j => fn A => 
                let val i = isub(dinv,j) in
                    dupdate(A, isub(f,i), 
                            dsub(A, isub(g,i)) + dsub(A, isub(h,i)))
                end )
            A
    end

