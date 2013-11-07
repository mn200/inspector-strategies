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
        (fn i => fn B => update(B, i, sub(C, sub(f,i)) + sub(C, sub(f,i))))
        B


(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val f = list_to_mvector [0,1,2,3,4]

val g = list_to_mvector [4,3,2,1,0]

val C = list_to_mvector [10,20,30,40,50]

orgcode (empty_v,C,f,g,5)

