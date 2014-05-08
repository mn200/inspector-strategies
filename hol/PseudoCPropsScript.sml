open HolKernel Parse boolLib bossLib;

open lcsymtacs

open bagTheory
open PseudoCTheory

val _ = new_theory "PseudoCProps";

val expr_weight_def = Define`
  (expr_weight (Value v) = 0:num) ∧
  (expr_weight e = 1)
`;
val _ = export_rewrites ["expr_weight_def"]

val dexpr_weight_def = Define`
  (dexpr_weight (DValue v) = 0:num) ∧
  (dexpr_weight (Read v e) = 1 + expr_weight e) ∧
  (dexpr_weight (Convert e) = expr_weight e)
`;
val _ = export_rewrites ["dexpr_weight_def"]

val stmt_weight_def = tDefine "stmt_weight" `
  (stmt_weight Abort = 0) ∧
  (stmt_weight Done = 0) ∧
  (stmt_weight (Assign w ds v) =
     1 + expr_weight (SND w) + SUM (MAP dexpr_weight ds)) ∧
  (stmt_weight (AssignVar v e) = 1) ∧
  (stmt_weight (Malloc v d value) = 1) ∧
  (stmt_weight (IfStmt g t e) = MAX (stmt_weight t) (stmt_weight e) + 1) ∧
  (stmt_weight (ForLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (ParLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (Seq stmts) =
    SUM (MAP (λms. stmt_weight (SND ms)) stmts) + 1 + LENGTH stmts) ∧
  (stmt_weight (Par stmts) =
    SUM (MAP (λms. stmt_weight (SND ms)) stmts) + 1 + LENGTH stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["stmt_weight_def"]

val loopbag_def = tDefine "loopbag" `
  (loopbag Abort = {| 0 |}) ∧
  (loopbag Done = {| 0 |}) ∧
  (loopbag (Assign w ds v) = {| 0 |}) ∧
  (loopbag (AssignVar v e) = {| 0 |}) ∧
  (loopbag (Malloc v d value) = {| 0 |}) ∧
  (loopbag (IfStmt g t e) = BAG_UNION (loopbag t) (loopbag e)) ∧
  (loopbag (ForLoop v d s) = BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (ParLoop v d s) = BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (Seq stmts) =
     FOLDR (λms b. BAG_UNION (loopbag (SND ms)) b) {|0|} stmts) ∧
  (loopbag (Par stmts) =
     FOLDR (λms b. BAG_UNION (loopbag (SND ms)) b) {|0|} stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["loopbag_def"]

val FINITE_loopbag = store_thm(
  "FINITE_loopbag[simp]",
  ``∀s. FINITE_BAG (loopbag s)``,
  ho_match_mp_tac (theorem "loopbag_ind") >>
  simp[] >> Induct >> simp[]);

val loopbag_not_empty = store_thm(
  "loopbag_not_empty[simp]",
  ``∀s. loopbag s ≠ {||}``,
  ho_match_mp_tac (theorem "loopbag_ind") >> simp[] >>
  Induct >> simp[]);

val MAX_PLUS = store_thm(
  "MAX_PLUS",
  ``MAX x y + z = MAX (x + z) (y + z)``,
  rw[arithmeticTheory.MAX_DEF]);

val transitive_LT = store_thm(
  "transitive_LT[simp]",
  ``transitive ((<) : num -> num -> bool)``,
  simp[relationTheory.transitive_def]);


val SUM_IMAGE_CONG = REWRITE_RULE [GSYM AND_IMP_INTRO] pred_setTheory.SUM_IMAGE_CONG
val BAG_CARD_SUM_IMAGE = store_thm(
  "BAG_CARD_SUM_IMAGE",
  ``FINITE_BAG b ==>
    (BAG_CARD b = SUM_IMAGE b { e | BAG_IN e b })``,
  Q.ID_SPEC_TAC `b` THEN Induct_on `FINITE_BAG` THEN
  SRW_TAC [][pred_setTheory.SUM_IMAGE_THM, BAG_CARD_THM] THEN
  SIMP_TAC (srw_ss()) [BAG_INSERT, pred_setTheory.GSPEC_OR] THEN
  `{ e | BAG_IN e b} = SET_OF_BAG b`
    by SRW_TAC [][SET_OF_BAG, pred_setTheory.EXTENSION] THEN
  SRW_TAC[][pred_setTheory.SUM_IMAGE_UNION,
            pred_setTheory.SUM_IMAGE_THM] THEN
  Cases_on `e IN SET_OF_BAG b` THENL [
    SRW_TAC[][pred_setTheory.INSERT_INTER, pred_setTheory.SUM_IMAGE_THM] THEN
    `SET_OF_BAG b = e INSERT (SET_OF_BAG b DELETE e)`
      by (SRW_TAC[][pred_setTheory.EXTENSION] THEN METIS_TAC[IN_SET_OF_BAG])THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SRW_TAC [][pred_setTheory.SUM_IMAGE_THM] THEN
    SRW_TAC[ARITH_ss][] THEN
    SRW_TAC[][Cong SUM_IMAGE_CONG],
    SRW_TAC [][pred_setTheory.INSERT_INTER, pred_setTheory.SUM_IMAGE_THM] THEN
    `!x. x IN SET_OF_BAG b ==> x <> e` by METIS_TAC[] THEN
    SRW_TAC[][Cong SUM_IMAGE_CONG] THEN
    `b e = 0` suffices_by SRW_TAC[ARITH_ss][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [BAG_IN, BAG_INN]
  ]);

val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ inv_image (mlt (<) LEX (<)) (λ(m,lm,s). (loopbag s, stmt_weight s)) b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[pairTheory.LEX_DEF, pred_setTheory.MAX_SET_THM]
  >- (Induct_on `rest` >> simp[])
  >- (Induct_on `rest` >> simp[])
  >- (Cases_on `b` >> simp[])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (simp[listTheory.SUM_APPEND] >> Cases_on `expr` >> fs[isValue_def])
  >- simp[listTheory.SUM_APPEND]
  >- (disj1_tac >> pop_assum kall_tac >>
      simp[mlt_dominates_thm1, rich_listTheory.FOLDR_MAP] >>
      conj_tac >- (Induct_on `iters` >> simp[]) >>
      qexists_tac `BAG_IMAGE SUC (loopbag body)` >> simp[] >>
      dsimp[dominates_def] >>
      qho_match_abbrev_tac
        `∀e1. BAG_IN e1 FF ⇒ ∃e2. BAG_IN e2 (loopbag body) /\ e1 < SUC e2` >>
      `∀e. BAG_IN e FF ⇒ BAG_IN e (loopbag body) ∨ e = 0`
        by (simp[Abbr`FF`] >> Induct_on `iters` >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> res_tac >- metis_tac[DECIDE ``x < SUC x``] >> simp[] >>
      metis_tac[loopbag_not_empty, BAG_cases, BAG_IN_BAG_INSERT])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (disj1_tac >> pop_assum kall_tac >>
      simp[rich_listTheory.FOLDR_MAP, mlt_dominates_thm1] >>
      conj_tac >- (Induct_on `iters` >> simp[]) >>
      qexists_tac `BAG_IMAGE SUC (loopbag body)` >> simp[] >>
      dsimp[dominates_def] >>
      qho_match_abbrev_tac
        `∀e1. BAG_IN e1 FF ⇒ ∃e2. BAG_IN e2 (loopbag body) ∧ e1 < SUC e2` >>
      `∀e. BAG_IN e FF ⇒ BAG_IN e (loopbag body) ∨ e = 0`
         by (simp[Abbr`FF`] >> Induct_on `iters` >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> res_tac >- metis_tac[DECIDE ``x < SUC x``] >>
      simp[] >>
      metis_tac[loopbag_not_empty, BAG_cases, BAG_IN_BAG_INSERT])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
      Induct_on `sfx` >> simp[])
  >- (disj2_tac >> simp[listTheory.SUM_APPEND] >> rw[] >>
      Induct_on `pfx` >> simp[]) >>
  disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
  Induct_on `sfx` >> simp[])

val _ = export_theory();
