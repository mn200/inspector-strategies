use "variants1Dloop.sml";

(******************************************************************************)
(* Some testing for primitives *)
val iupdate_test1 =
    ivector_to_list( iupdate( empty_iv(Domain1D(0,3),Domain1D(0,7),Tuple1D(0)),
                              Tuple1D(2), Tuple1D(42))) = [0,0,42]

val dupdate_test1 =
    dvector_to_list(dupdate( empty_dv(Domain1D(0,3),false), Tuple1D(1), true)) 
    = [false,true,false]


(******************************************************************************)
(******************************************************************************)
(***** Testing for the original loop with no deps and all of the variants *****)
(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val f = list_to_ivector [1,2,3,4,0] (Domain1D(0,5))

val g = list_to_ivector [4,3,2,1,0] (Domain1D(0,5))

val C = list_to_dvector [10,20,30,40,50]
(*
val test_org = dvector_to_list(orgcode (empty_dv(idomx(f),0),C,f,g,5)) 
               = [70,70,70,70,20]

val er_test1 = mrel_to_list(construct_explicit_relation(5,5,f,g))
*)
val inspec_test1 = 
    ivector_to_list(
        cpack_inspector( 
            construct_explicit_relation(Domain1D(0,5),Domain1D(0,5),f,g)))
    = [4,0,3,1,2]
(*
val variant1_out = dvector_to_list(
        codevariant1(empty_dv(idomx(f),0),C,f,g,5,5))
*)
val variant1_test1 = dvector_to_list(orgcode(empty_dv(idomx(f),0),C,f,g,5)) 
                     = dvector_to_list(
                         codevariant1(empty_dv(idomx(f),0),C,f,g,5,5))

(* Test where packing needs to do a cleanup pass *)
(* Well no because output of original code doesn't depend on index 2
 * if it just isn't there *)
val f = list_to_ivector [1,1,3,3,0] (Domain1D(0,5))

val g = list_to_ivector [4,4,1,1,0] (Domain1D(0,5))

val C = list_to_dvector [10,20,30,40,50]

val variant1_test2 = dvector_to_list(orgcode(empty_dv(idomx(f),0),C,f,g,5)) 
                     = dvector_to_list(
                         codevariant1(empty_dv(idomx(f),0),C,f,g,5,5))

(* What about the output from the inspector? *)
val inspec_test2 = 
    ivector_to_list(
        cpack_inspector(
            construct_explicit_relation(Domain1D(0,5),Domain1D(0,5),f,g)))
    = [4,0,1,2,3]

(* Test 3: Another example.  Now N=3 and M=5.  C can stay the same. *)
val fsz3 =  list_to_ivector [0,4,3] (Domain1D(0,5))
val gsz3 =  list_to_ivector [1,4,2] (Domain1D(0,5))
val debug = (print("domain_size(idomx(fsz3)) = "^Int.toString(size_domain(idomx(fsz3)))^"\n"); fsz3)
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
                         orgcode(empty_dv(idomx(fsz3),0),C,fsz3,gsz3,3)) 
                     = dvector_to_list(
                         codevariant1(empty_dv(idomx(fsz3),0),C,fsz3,gsz3,3,5))
val debug = (print("after variant1_test3\n");0)

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
val f = list_to_ivector [1,2,1,4,0] (Domain1D(0,5)) (* writes *)
val g = list_to_ivector [4,3,2,1,0] (Domain1D(0,5)) (* reads *)
val h = list_to_ivector [0,1,2,3,4] (Domain1D(0,5)) (* reads *)
(* Deps should have
 *      anti: (0,3),(0,4),(1,2)
 *      flow: (0,1),(1,2),(2,3),(3,4),(0,3)
 *      output: (0,2)
 *)
val R_A = construct_R_A(Domain1D(0,N),Domain1D(0,M),g,h)
val test_R_A = mrel_to_list( R_A )
val W_A = construct_W_A(Domain1D(0,N),Domain1D(0,M),f)
val test_W_A = mrel_to_list( W_A )
val test_Deps = mrel_to_list(construct_Deps(Domain1D(0,N),R_A,W_A))

(* Of course above example results in a full order. *)
(* Here is an example that doesn't. *)
val f = list_to_ivector [1,2,1,2,1] (Domain1D(0,5)) (* writes *)
val g = list_to_ivector [4,3,4,3,4] (Domain1D(0,5)) (* reads *)
val h = list_to_ivector [0,3,0,3,0] (Domain1D(0,5)) (* reads *)
val R_A2 = construct_R_A(Domain1D(0,N),Domain1D(0,M),g,h)
val test_R_A2 = mrel_to_list( R_A2 )
val W_A2 = construct_W_A(Domain1D(0,N),Domain1D(0,M),f)
val test_W_A2 = mrel_to_list( W_A2 )
val test_Deps2 = mrel_to_list(construct_Deps(Domain1D(0,N),R_A2,W_A2))

(* Now let's do the actual computation *)
val A = list_to_dvector [10,20,30,40,50]
val test_org_with_deps = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
               = [10,60,80,40,50]
val debug = (print("after test_org_with_deps\n");0)

(* testing the topological inspectors *)
val top_test1 = 
    ivector_to_list(topological_inspector(
                         construct_Deps(Domain1D(0,N),R_A2,W_A2)))
    = [0,1,2,3,4]
val debug = (print("after topologlical_inspector\n");0)

val fast_top_test1 =
    ivector_to_list(fast_top_inspector(R_A2,W_A2))
    = [0,1,2,3,4]
val debug = (print("after ivector_to_list\n");0)

(* above example results in permutation equal to original order *)
(* here is another example where should get 0,3,1,4,2 *)
val f = list_to_ivector [1,1,1,2,2] (Domain1D(0,5)) (* writes *)
val g = list_to_ivector [4,3,4,3,4] (Domain1D(0,5)) (* reads *)
val h = list_to_ivector [0,3,0,3,0] (Domain1D(0,5)) (* reads *)
val R_A2 = construct_R_A(Domain1D(0,N),Domain1D(0,M),g,h)
val test_R_A2 = mrel_to_list( R_A2 )
val W_A2 = construct_W_A(Domain1D(0,N),Domain1D(0,M),f)
val test_W_A2 = mrel_to_list( W_A2 )
val test_Deps2 = mrel_to_list(construct_Deps(Domain1D(0,N),R_A2,W_A2))
val debug = (print("after some construct_*_As\n");0)

val top_test2 = 
    ivector_to_list(topological_inspector(
                         construct_Deps(Domain1D(0,N),R_A2,W_A2)))
    (*= [0,3,1,4,2]*)
val debug = (print("after construct_Deps\n");0)

val fast_top_test2 =
    ivector_to_list(fast_top_inspector(R_A2,W_A2))
    = [0,3,1,4,2]

val variant2_out = dvector_to_list(codevariant2(A,f,g,h,N,M))
val debug = (print("after variant2_out\n");0)

val variant2_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant2(A,f,g,h,N,M))
val debug = (print("after variant2_test2\n");0)

val variant3_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant3(A,f,g,h,N,M))
val debug = (print("after variant3_test2\n");0)

val variant4_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                     = dvector_to_list(codevariant4(A,f,g,h,N,M))
val debug = (print("after variant4_test2\n");0)


(******************************************************************************)
(******************************************************************************)
(***** Testing for the original loop with no deps and all of the variants *****)
(* Using the origcode requires initializing B, C, f, g, and N with values. *)

val f = list_to_ivector [1,1,3,3,0] (Domain1D(0,5))

val g = list_to_ivector [4,4,1,1,0] (Domain1D(0,5))

val C = list_to_dvector [10,20,30,40,50]

(**** dopar_reord tests *)

val dopar_reord_test1 =
    dvector_to_list(
        orgcode(empty_dv(idomx(f),0),C,f,g,size_domain(ddomx(C))))
    = dvector_to_list(
        codevariant_dopar_reord(empty_dv(idomx(f),0),C,f,g,cpack_inspector))
val debug = (print("after dopar_reord_test1\n");0)


(***** Testing for the original loop with deps and all of the variants *****)
(* Original Code in C for loop with deps
 *
 *   for (i=0; i<N; i++) {
 *     A[ f[i] ] =  A[ g[i] ] + A[ h[i] ];
 *   }
 *)

val N = 5
val M = 5
val f = list_to_ivector [1,2,1,3,4] (Domain1D(0,5)) (* writes *)
val g = list_to_ivector [0,0,2,0,0] (Domain1D(0,5)) (* reads *)
val h = list_to_ivector [0,0,0,0,1] (Domain1D(0,5)) (* reads *)
(* Deps are
 *      anti: (0,4), (2,4)
 *      flow: (1,2)
 *      output: (0,2)
 *)


(**** doacross_reord tests ****)
val single_wave = fn (_,_) => empty_iv(Domain1D(0,N),Domain1D(0,1),Tuple1D(0))
val no_reord = fn _ =>
                  FOR (Domain1D(0,N))
                      (fn i => fn dinv => iupdate (dinv, i, i) )
                      (empty_iv(Domain1D(0,N),Domain1D(0,N),Tuple1D(0)))

(* Both the wavefront function and reordering function do nothing interesting *)
val doacross_reord_test1 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                           = dvector_to_list(
                               codevariant_doacross_reord(A,f,g,h,N,M,
                                                          single_wave,
                                                          no_reord))
val debug = (print("after doacross_reord_test1\n");0)


(* Using simple pack routine even though all iteration just put in same wave. *)
val doacross_reord_test2 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                           = dvector_to_list(
                               codevariant_doacross_reord(A,f,g,h,N,M,
                                                          single_wave,
                                                          pack_waves_simple))
val debug = (print("after doacross_reord_test2\n");0)


(* Using count sort pack routine.  All iters still in one wave. *)
val doacross_reord_test3 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                           = dvector_to_list(
                               codevariant_doacross_reord(A,f,g,h,N,M,
                                                          single_wave,
                                                          pack_waves_fast))
val debug = (print("after doacross_reord_test3\n");0)


(* Using count sort pack routine.  Finding waves without Deps. *)
val doacross_reord_test4 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                           = dvector_to_list(
                               codevariant_doacross_reord(A,f,g,h,N,M,
                                                          find_waves_fast,
                                                          pack_waves_fast))
val debug = (print("after doacross_reord_test4\n");0)


(* Using count sort pack routine.  Finding waves with Deps. *)
val doacross_reord_test5 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                           = dvector_to_list(
                               codevariant_doacross_reord(A,f,g,h,N,M,
                                                          find_waves_deps,
                                                          pack_waves_fast))
val debug = (print("after doacross_reord_test5\n");0)


(**** dota_reord tests ****)
val data_reord_test1 = dvector_to_list(orgcode_with_deps(A,f,g,h,N)) 
                       = dvector_to_list(
                           codevariant_data_reord(A,f,g,h,
                                                  data_permute_inspector))

val debug = (print("after data_reord_test1\n");0)
