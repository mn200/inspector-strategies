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

val FOR_RULE = store_thm(
  "FOR_RULE",
  ``Inv lo A ∧ (∀i a. lo ≤ i ∧ i < hi ∧ Inv i a ⇒ Inv (i + 1) (f i a)) ∧
    (∀j a. hi ≤ j ∧ Inv j a ⇒ P a)
   ⇒
    P (FOR (lo,hi) f A)``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- srw_tac[ARITH_ss][Once FOR_def] >>
  srw_tac[ARITH_ss][FOR_nonzero]);

val vsz_update_FOR = store_thm(
  "vsz_update_FOR",
  ``∀A. vsz (FOR (lo, hi) (λi a. update a (f i a) (g i a)) A) = vsz A``,
  strip_tac >> DEEP_INTRO_TAC FOR_RULE >> qexists_tac `λi a. vsz a = vsz A` >>
  srw_tac[][]);

val range_CONG = store_thm(
  "range_CONG",
  ``(!i A. lo ≤ i ∧ i < hi ⇒ (f i A = f' i A)) ⇒
    FOR (lo, hi) f B = FOR (lo,hi) f' B``,
  qid_spec_tac `B` >> Induct_on `hi - lo`
  >- (ONCE_REWRITE_TAC [FOR_def] >> srw_tac[ARITH_ss][]) >>
  rpt strip_tac >> srw_tac[ARITH_ss][FOR_nonzero]);

val _ = export_theory();
