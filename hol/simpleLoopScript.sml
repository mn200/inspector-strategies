open HolKernel Parse boolLib bossLib;

open pred_setTheory primitivesTheory
open lcsymtacs

val _ = new_theory "simpleLoop";

(* a "simple loop" is an array calculation that looks like

    for (i=0; i < N; i++)
      A[i] = ....i....A[i]....

   where the ....s can't contain any references to A, except that it
   is allowed to refer to A[i] (giving a "map" like calculation). It
   can also use the index i any other way it likes (in particular, for
   indexing into other arrays, say).

   In other words, the r.h.s of the assignment is allowed to look at
   both i and A ' i (HOL for A[i]), but not A in general.

   The C above is represented as

     FOR (0,N) (λi A. update A i (....i....A ' i...)) A

   where the ....s more or less correspond.

   The core result of this theory is that if Δ is a bijection
   (permutation) over the indices 0..N-1, then you can replace the
   loop above with

     for(i=0; i < N; i++)
       A[Δ[i]] = ...Δ[i]...A[Δ[i]]...

   The restrictions on occurrences mean that something like

     A[i] = A[i] + C[f[i+1]]     (ok)

   is fine as the loop body, but that

     A[i] = A[i-1] + C[i]        (notok)

   is not. If you'd gone to the trouble of copying A into some array
   oldA before the loop, you could certainly have

     A[i] = oldA[i-1] + C[i]

   as your body, but that's quite a different effect from the equation
   in (notok).

*)


val vsub_simple_update_out_range_FOR = store_thm(
  "vsub_simple_update_out_range_FOR",
  ``∀i A. i < lo ∨ hi ≤ i ∨ vsz A ≤ i ⇒ FOR (lo,hi) (λi a. update a i (g i a)) A ' i = A ' i``,
  rpt strip_tac >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λj a. vsz A = vsz a ∧ a ' i = A ' i` >>
  srw_tac[ARITH_ss][update_sub]);

val vsub_simple_update_in_range_FOR = store_thm(
  "vsub_simple_update_in_range_FOR",
  ``∀i A. lo ≤ i ∧ i < hi ∧ hi ≤ vsz A ⇒
          FOR (lo,hi) (λj a. update a j (g j)) A ' i = g i``,
  rpt strip_tac >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λj a. vsz a = vsz A ∧ ∀k. lo ≤ k ∧ k < j ⇒ a ' k = g k` >>
  asm_simp_tac (srw_ss() ++ ARITH_ss)[] >>
  map_every qx_gen_tac [`j`, `a`] >> strip_tac >>
  qx_gen_tac `k` >> strip_tac >>
  `k = j ∨ k < j` by decide_tac >> srw_tac[ARITH_ss][update_sub]);

val PERMS_suffice0 = prove(
  ``BIJ Δ (count N) (count N) ∧
    (final = FOR (0, N) (\i a. update a i (g i)) A1) ⇒
    ∀m n A2.
      (vsz A1 = vsz A2) ∧ N ≤ vsz A1 ∧
      (m = N - n) ∧ n ≤ N ∧
      (∀i. vsub A2 i = if i ∈ IMAGE Δ (count n) then vsub final i
                       else vsub A1 i)
     ⇒
      (FOR (n, N) (\i a. update a (Δ i) (g (Δ i))) A2 = final)``,
  strip_tac >> Induct >| [
    rpt strip_tac >> `N = n` by decide_tac >>
    qpat_assum `0 = N - n` kall_tac >>
    srw_tac[ARITH_ss][] >>
    srw_tac[ARITH_ss][vector_EQ, vsz_update_FOR] >>
    Cases_on `i < N`
    >- (`∃j. j < N ∧ (i = Δ j)`
          by metis_tac[BIJ_DEF, IN_COUNT, SURJ_DEF] >>
        rw[] >> metis_tac[]) >>
    srw_tac[ARITH_ss][vsub_simple_update_out_range_FOR],

    rpt strip_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    srw_tac[ARITH_ss][] >>
    fs[AND_IMP_INTRO] >> first_x_assum match_mp_tac >>
    srw_tac[ARITH_ss][] >| [
      Cases_on `x = n`
      >- (`Δ x < N`
            by (`n < N` by decide_tac >>
                metis_tac [BIJ_DEF, IN_COUNT, SURJ_DEF]) >>
            srw_tac[ARITH_ss][vsub_simple_update_in_range_FOR,
                              update_sub]) >>
      `x < n ∧ x < N ∧ n < N` by decide_tac >>
      `Δ x ≠ Δ n`
         by (fs[BIJ_DEF, IN_COUNT, INJ_DEF] >> metis_tac[]) >>
      srw_tac[][update_sub] >> metis_tac[],
      `i ≠ Δ n` by metis_tac[DECIDE ``n < n + 1``] >>
      srw_tac[][update_sub] >>
      metis_tac[DECIDE ``x < y ⇒ x < y + 1``]
    ]
  ]);

(* first lemma shows that an even simpler result holds. Here the loop
   body is not allowed to refer to A at all, not even at the index
   being updated.

 ⊢ BIJ Δ (count N) (count N) ∧ N ≤ vsz A ⇒
     FOR (0,N) (λi a. update a (Δ i) (g (Δ i))) A =
     FOR (0,N) (λi a. update a i (g i)) A:
*)

val PERMS_SUFFICE_simple = save_thm(
  "PERMS_SUFFICE_simple",
  PERMS_suffice0 |> Q.GEN `final`
                 |> SIMP_RULE (srw_ss()) []
                 |> UNDISCH
                 |> Q.SPECL [`0`, `A1`]
                 |> SIMP_RULE (srw_ss()) []
                 |> DISCH_ALL
                 |> REWRITE_RULE [AND_IMP_INTRO]
                 |> Q.INST [`A1` |-> `A`]);

(* next, we show that referring to the index being updated in any loop
   is equivalent to referring to the old value of the array if the
   indices simply sweep over the array once
*)

val simple_MAP = store_thm(
  "simple_MAP",
  ``FOR (lo,hi) (λi A. update A i (f i (A ' i))) A =
    FOR (lo,hi) (λi A'. update A' i (f i (A ' i))) A``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- (ONCE_REWRITE_TAC [FOR_def] >> srw_tac[ARITH_ss][]) >>
  rpt strip_tac >> srw_tac[ARITH_ss][FOR_nonzero] >>
  first_x_assum (qspecl_then [`hi`, `lo + 1`] mp_tac) >>
  asm_simp_tac arith_ss [] >>
  disch_then (qspec_then `update A lo (f lo (A ' lo))` mp_tac) >>
  disch_then SUBST_ALL_TAC >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [Cong range_CONG, update_sub]);

(* similarly, if your sweep over the array is mediated by a
   indirection array Δ, then as long as the Δ-function is injective,
   it's still OK to look at the value of the array at index Δ[i].

   The injectivity ensures that you never look at the same index
   twice, so that you only ever see an old value when you look at
   A[Δ[i]].
*)

val simple_MAP_INJ = store_thm(
  "simple_MAP_INJ",
  ``(∀i j. lo ≤ i ∧ i < hi ∧ lo ≤ j ∧ j < hi ⇒ (Δ i = Δ j ⇔ i = j)) ⇒
    FOR (lo,hi) (λi A. update A (Δ i) (f (Δ i) (A ' (Δ i)))) A =
    FOR (lo,hi) (λi A'. update A' (Δ i) (f (Δ i) (A ' (Δ i)))) A``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- (ONCE_REWRITE_TAC [FOR_def] >> srw_tac[ARITH_ss][]) >>
  rpt strip_tac >> srw_tac[ARITH_ss][FOR_nonzero] >>
  `v = hi - (lo + 1)` by decide_tac >>
  pop_assum (fn th => first_x_assum (fn pat => mp_tac (MATCH_MP pat th))) >>
  asm_simp_tac arith_ss [] >>
  disch_then (qspec_then `update A (Δ lo) (f (Δ lo) (A ' (Δ lo)))`
                         SUBST_ALL_TAC) >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [Cong range_CONG, update_sub]);


val lem0 = prove(
  ``BIJ Δ (count N) (count N) ∧ N ≤ vsz A ⇒
    ∀i j. 0 ≤ i ∧ i < N ∧ 0 ≤ j ∧ j < N ⇒ (Δ i = Δ j ⇔ i = j)``,
  REWRITE_TAC[BIJ_DEF, INJ_DEF, IN_COUNT] >> metis_tac[])
val lem1 = simple_MAP_INJ |> UNDISCH |> GSYM |> Q.INST [`lo` |-> `0`, `hi` |-> `N`]
                          |> PROVE_HYP (UNDISCH lem0)

(*
   ⊢ BIJ Δ (count N) (count N) ∧ N ≤ vsz A ⇒
     FOR (0,N) (λi A. update A (Δ i) (f (Δ i) (A ' (Δ i)))) A =
     FOR (0,N) (λi A. update A i (f i (A ' i))) A:

  Instantiate f with

    λi e. e + C[f[i + 1]]

  to get the (ok) loop of the introductory comment above.

*)
val PERMS_SUFFICE = save_thm(
  "PERMS_SUFFICE",
  PERMS_SUFFICE_simple |> Q.INST [`g` |-> `λj. f j (A ' j)`]
                       |> UNDISCH
                       |> BETA_RULE
                       |> REWRITE_RULE [lem1]
                       |> SIMP_RULE bool_ss [GSYM simple_MAP]
                       |> DISCH_ALL);

val _ = export_theory();
