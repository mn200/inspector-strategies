(* variants1Dloop.sml *)

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

(* Original Code in C
 *
 * for (i=0; i<N; i++) {
 *     B[i] = C[ f[i] ] + C[ g[i] ];
 * }
 *)
fun orgcode (B,C,f,g,N) =
    FOR (0,N)
        (fn i => fn B => update(B, i, sub(C, sub(f,i)) + sub(C, sub(g,i))))
        B

(* Variant 1
 * Transformed code in C, using cpack heuristic to reorder iterations
 *     T = { [i] -> [j] | j=d(i) } is transformation specification
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
        (fn i => fn E => r_update(r_update(E,sub(f,i),i), sub(g,i),i))
        (empty_r (M,N))


(* Using 0 and 1 for false and true because that is what mvector handles. *)
fun inspector (E) =
    let 
        val visited = FOR (0,rsizey(E))
                          (fn i => fn visited => update(visited, i, 0) )
                          empty_v
        (*fun pack_i_in_E E = 
                      FOR (0,rsizex(E))
                          (fn i => fn (dinv,visited) =>
                              (foldl 
                                (fn (y,(dinv,visited)) =>
                                  if 0=sub(visited,y)
                                  then (update(dinv, size(dinv), y),
                                        update(visited, y, 1))
                                  else (dinv,visited))
                                (dinv,visited)  (mrel_at_x E i) ) )
                          (empty_v,visited)*)
        val (dinv,visited) = 
	    RFOR X 
		 (fn (x,y) => fn (dinv,visited) =>
		     if 0=sub(visited,y)
	             then ( update(dinv,size(dinv),y), update(visited, y, 1) )
                     else ( dinv, visited ) )
                 E
		 (empty_v,visited)
    in
        dinv
    end 

(* N is number of iterations, M is size of dataspaces *)
fun codevariant1 (B,C,f,g,N,M) =
    let
	val E = construct_explicit_relation(M,N,f,g)
	val dinv = inspector(E)
    in

	FOR (0,N)
            (fn j => fn B => 
                let val i = sub(dinv,j) in
	            update(B, i, sub(C, sub(f,i)) + sub(C, sub(g,i)))
                end )
            B
    end


(***** Testing for the original and all of the variants *****)
(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val f = list_to_mvector [1,2,3,4,0]

val g = list_to_mvector [4,3,2,1,0]

val C = list_to_mvector [10,20,30,40,50]

val test_org = mvector_to_list(orgcode (empty_v,C,f,g,5)) = [70,70,70,70,20]

val variant1_test1 = mvector_to_list(orgcode(empty_v,C,f,g,5)) 
                     = mvector_to_list(codevariant1(empty_v,C,f,g,5,5))

(* Test where packing needs to do a cleanup pass *)
(* Well no because output of original code doesn't depend on index 2
 * if it just isn't there *)
val f = list_to_mvector [1,1,3,3,0]

val g = list_to_mvector [4,4,1,1,0]

val C = list_to_mvector [10,20,30,40,50]

val variant1_test2 = mvector_to_list(orgcode(empty_v,C,f,g,5)) 
                     = mvector_to_list(codevariant1(empty_v,C,f,g,5,5))

(* What about the output from the inspector? *)
val inspec_test2 = 
    mvector_to_list(inspector( construct_explicit_relation(5,5,f,g)))
    = [4,0,1,2,3]

(* Test 3: Another example.  Now N=3 and M=5.  C can stay the same. *)
val fsz3 =  list_to_mvector [0,4,3]
val gsz3 =  list_to_mvector [1,4,2]

val er_test3 = 
    mrel_to_list ( construct_explicit_relation(5,3,fsz3,gsz3) )
    =  [(4,1),(3,2),(2,2),(1,0),(0,0)]

(* Used for debugging.
val E = construct_explicit_relation(5,3,fsz3,gsz3);
val xsize = rsize_for_x(E);
val ysize = rsize_for_y(E);
val inspec_test3 = 
    mvector_to_list(inspector( construct_explicit_relation(5,3,fsz3,gsz3)))
*)
val variant1_test3 = mvector_to_list(orgcode(empty_v,C,fsz3,gsz3,3)) 
                     = mvector_to_list(codevariant1(empty_v,C,fsz3,gsz3,3,5))

