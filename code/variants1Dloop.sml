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


(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val f = list_to_mvector [0,1,2,3,4]

val g = list_to_mvector [4,3,2,1,0]

val C = list_to_mvector [10,20,30,40,50]

val test1_org = mvector_to_list(orgcode (empty_v,C,f,g,5)) = [60,60,60,60,60]

(* Transformed code in C, using cpack heuristic to reorder iterations
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
 * for (i=0; i<N; i++) {  \\ check that everyone got reordered
 *   if (!visited[i]) { dinv[count++] = i; }
 *
 * // transformed executor
 * for (j=0; j<N; j++) {
 *     B[dinv[j]] = C[ f[dinv[j]] ] + C[ g[dinv[j]] ];
 * }
 *)
