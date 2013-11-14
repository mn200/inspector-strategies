open HolKernel Parse boolLib bossLib;

open lcsymtacs
open pred_setTheory

val _ = new_theory "primitives";

val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("mvector", ``:(num -> 'a) # num``)

val FOR_def = TotalDefn.tDefine "FOR" `
  FOR (lo,hi) body A = if lo < hi then FOR (lo+1,hi) body (body lo A)
                       else A
` (WF_REL_TAC `measure (λ(lohi,b,A). SND lohi - FST lohi)`)

val FOR_0 = store_thm(
  "FOR_0",
  ``FOR (x,x) f A = A``,
  rw[Once FOR_def]);
val _ = export_rewrites ["FOR_0"]

val FOR_nonzero = store_thm(
  "FOR_nonzero",
  ``lo < hi ⇒ FOR (lo,hi) f A = FOR (lo + 1, hi) f (f lo A)``,
  rw[Once FOR_def, SimpLHS])

val FOR_ind = save_thm(
  "FOR_ind",
  theorem "FOR_ind"
          |> Q.SPEC `λp f A. Q (FST p) (SND p) f A`
          |> SIMP_RULE (srw_ss()) []
          |> Q.GEN `Q`);

val FOR_SUC_shift = store_thm(
  "FOR_SUC_shift",
  ``∀i j f A.
      FOR (SUC i, SUC j) f A = FOR (i, j) (λi a. f (SUC i) a) A``,
  NTAC 2 GEN_TAC >> Induct_on `j - i` THEN rpt strip_tac >| [
    `j <= i` by decide_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    SRW_TAC[ARITH_ss][],
    `i < j` by decide_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    SRW_TAC[ARITH_ss][GSYM arithmeticTheory.ADD1]
  ]);

val update_def = Define`
  update (mv,sz) d r = if d < sz then ((d =+ r) mv, sz) else (mv, sz)
`;

val vsub_def = Define`vsub (mv,sz) d = mv d`

val _ = set_fixity "'" (Infixl 2000)
val _ = overload_on ("'", ``vsub``)
val _ = overload_on ("vsz", ``SND : (num -> 'a) # num -> num``)

val list_to_mvector_def = Define`
  list_to_mvector l = ((λi. EL i l), LENGTH l)
`;

val mvector_to_list_def = Define`
  mvector_to_list (f,sz) = REVERSE (FOR (0,sz) (λi l. f i :: l) [])
`;

(* e.g. *)
val _ = EVAL ``mvector_to_list (list_to_mvector [1;2;3;4])``

val mvector_list_ISO = store_thm(
  "mvector_list_ISO",
  ``mvector_to_list (list_to_mvector l) = l``,
  SRW_TAC[][mvector_to_list_def, list_to_mvector_def] THEN
  `∀l A. REVERSE (FOR (0,LENGTH l) (λi l0. EL i l :: l0) A) = REVERSE A ++ l`
    suffices_by rw[] >>
  Induct_on `l` >> rw[Once FOR_def] >>
  simp_tac bool_ss [arithmeticTheory.ONE, FOR_SUC_shift] >>
  simp[]);

val vector_EQ = store_thm(
  "vector_EQ",
  ``v1 : 'a mvector = v2 ⇔ (∀i. v1 ' i = v2 ' i) ∧ vsz v1 = vsz v2``,
  Cases_on `v1` >> Cases_on `v2` >> rw[vsub_def, FUN_EQ_THM]);

val update_sub = store_thm(
  "update_sub",
  ``update A j x ' i = if i = j ∧ j < vsz A then x
                       else A ' i``,
  Cases_on `A` >> rw[update_def, vsub_def, combinTheory.UPDATE_APPLY] >>
  fs[combinTheory.UPDATE_APPLY]);

val vsz_update = store_thm(
  "vsz_update",
  ``vsz (update a i x) = vsz a``,
  Cases_on `a` >> rw[update_def]);
val _ = export_rewrites ["vsz_update"]

val vsz_update_FOR = store_thm(
  "vsz_update_FOR",
  ``∀A. vsz (FOR (lo, hi) (λi a. update a (f i a) (g i a)) A) = vsz A``,
  Induct_on `hi - lo` >> ONCE_REWRITE_TAC [FOR_def] >>
  srw_tac[ARITH_ss][]);

val vsub_simple_update_out_range_FOR = store_thm(
  "vsub_simple_update_out_range_FOR",
  ``∀i A. i < lo ∨ hi ≤ i ⇒ FOR (lo,hi) (λi a. update a i (g i a)) A ' i = A ' i``,
  Induct_on `hi - lo` >> srw_tac[ARITH_ss][Once FOR_def] >>
  srw_tac[ARITH_ss][update_sub]);

val vsub_simple_update_in_range_FOR = store_thm(
  "vsub_simple_update_in_range_FOR",
  ``∀i A. lo ≤ i ∧ i < hi ∧ hi ≤ vsz A ⇒
          FOR (lo,hi) (λj a. update a j (g j)) A ' i = g i``,
  Induct_on `hi - lo` >- srw_tac[ARITH_ss][Once FOR_def] >>
  rpt strip_tac >> srw_tac[ARITH_ss][Once FOR_def] >>
  `i = lo ∨ lo + 1 ≤ i ∧ i < hi` by decide_tac
  >- srw_tac[ARITH_ss][vsub_simple_update_out_range_FOR, update_sub] >>
  srw_tac[ARITH_ss][]);

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

(*
 ⊢ BIJ Δ (count N) (count N) ∧ N ≤ vsz A ⇒
     FOR (0,N) (λi a. update a (Δ i) (g (Δ i))) A =
     FOR (0,N) (λi a. update a i (g i)) A:
*)

val PERMS_SUFFICE = save_thm(
  "PERMS_SUFFICE",
  PERMS_suffice0 |> Q.GEN `final`
                 |> SIMP_RULE (srw_ss()) []
                 |> UNDISCH
                 |> Q.SPECL [`0`, `A1`]
                 |> SIMP_RULE (srw_ss()) []
                 |> DISCH_ALL
                 |> REWRITE_RULE [AND_IMP_INTRO]
                 |> Q.INST [`A1` |-> `A`]);

val _ = export_theory();
