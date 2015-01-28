open HolKernel Parse boolLib bossLib;

open lcsymtacs
val _ = new_theory "forLoop";

val _ = ParseExtras.tight_equality()

val SAT_ss = SatisfySimps.SATISFY_ss
val _ = augment_srw_ss [SAT_ss]


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

val FOR_RULE = store_thm(
  "FOR_RULE",
  ``Inv lo A ∧ (∀i a. lo ≤ i ∧ i < hi ∧ Inv i a ⇒ Inv (i + 1) (f i a)) ∧
    (∀j a. hi ≤ j ∧ Inv j a ⇒ P a)
   ⇒
    P (FOR (lo,hi) f A)``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- srw_tac[ARITH_ss][Once FOR_def] >>
  srw_tac[ARITH_ss][FOR_nonzero]);

val _ = export_theory();
