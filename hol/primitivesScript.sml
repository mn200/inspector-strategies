open HolKernel Parse boolLib bossLib;

open lcsymtacs

val _ = new_theory "primitives";

val _ = type_abbrev ("mvector", ``:(num -> 'a) # num``)

val FOR_def = TotalDefn.tDefine "FOR" `
  FOR (lo,hi) body A = if lo < hi then FOR (lo+1,hi) body (body lo A)
                       else A
` (WF_REL_TAC `measure (λ(lohi,b,A). SND lohi - FST lohi)`)

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
  ``(v1 : 'a mvector = v2) ⇔ (∀i. v1 ' i = v2 ' i) ∧ (vsz v1 = vsz v2)``,
  Cases_on `v1` >> Cases_on `v2` >> rw[vsub_def, FUN_EQ_THM]);

val update_sub = store_thm(
  "update_sub",
  ``update A j x ' i = if (i = j) ∧ j < vsz A then x
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

val vsub_simple_update_FOR = store_thm(
  "vsub_simple_update_FOR",
  ``∀i A. hi ≤ i ⇒ (FOR (lo,hi) (λi a. update a i (g i a)) A ' i = A ' i)``,
  Induct_on `hi - lo` >> srw_tac[ARITH_ss][Once FOR_def] >>
  srw_tac[ARITH_ss][update_sub]);

(*
val PERMS_suffice = store_thm(
  "PERMS_suffice",
  ``BIJ Δ (count N) (count N) ∧
    (final = FOR (0, N) (\i a. update a i (g i)) A1) ⇒
    ∀m n A2.
      (vsz A1 = vsz A2) ⇒
      (m = N - n) ∧ n ≤ N ∧
      (∀i. vsub A2 i = if i ∈ IMAGE Δ (count n) then vsub final i
                       else vsub A1 i)
     ⇒
      (FOR (n, N) (\i a. update a (Δ i) (g (Δ i))) A2 = final)``,
  strip_tac >> Induct >| [
    rpt strip_tac >> `N = n` by decide_tac >>
    qpat_assum `0 = N - n` kall_tac >>
    srw_tac[ARITH_ss][Once FOR_def] >>
    srw_tac[ARITH_ss][vector_EQ] >| [
      Cases_on `i < N`
      >- (`∃j. j < N ∧ (i = Δ j)`
            by metis_tac[pred_setTheory.BIJ_DEF, pred_setTheory.IN_COUNT,
                         pred_setTheory.SURJ_DEF] >>
          rw[] >> metis_tac[]) >>
      `¬∃j. (i = Δ j) ∧ j < N`
        suffices_by srw_tac[ARITH_ss][vsub_simple_update_FOR] >>
      metis_tac[pred_setTheory.BIJ_DEF, pred_setTheory.IN_COUNT,
                pred_setTheory.SURJ_DEF],
      rw[vsz_update_FOR]
    ],
    rpt strip_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    srw_tac[ARITH_ss][] >>
    fs[AND_IMP_INTRO] >> first_x_assum match_mp_tac >>
    srw_tac[ARITH_ss][]

*)



val _ = export_theory();
