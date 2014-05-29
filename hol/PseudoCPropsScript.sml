open HolKernel Parse boolLib bossLib;

open lcsymtacs

open bagTheory
open PseudoCTheory
open actionGraphTheory
open pred_setTheory finite_mapTheory
open intLib

val _ = new_theory "PseudoCProps";

val expr_weight_def = Define`
  (expr_weight (Value v) = 0:num) ∧
  (expr_weight e = 1)
`;
val _ = export_rewrites ["expr_weight_def"]

val dexpr_weight_def = Define`
  (dexpr_weight (DValue v) = 0:num) ∧
  (dexpr_weight (ARead v e) = 1 + expr_weight e) ∧
  (dexpr_weight (VRead v) = 1)
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


val SUM_IMAGE_CONG = REWRITE_RULE [GSYM AND_IMP_INTRO] SUM_IMAGE_CONG
val BAG_CARD_SUM_IMAGE = store_thm(
  "BAG_CARD_SUM_IMAGE",
  ``FINITE_BAG b ==>
    (BAG_CARD b = SUM_IMAGE b { e | BAG_IN e b })``,
  Q.ID_SPEC_TAC `b` THEN Induct_on `FINITE_BAG` THEN
  SRW_TAC [][SUM_IMAGE_THM, BAG_CARD_THM] THEN
  SIMP_TAC (srw_ss()) [BAG_INSERT, GSPEC_OR] THEN
  `{ e | BAG_IN e b} = SET_OF_BAG b`
    by SRW_TAC [][SET_OF_BAG, EXTENSION] THEN
  SRW_TAC[][SUM_IMAGE_UNION,
            SUM_IMAGE_THM] THEN
  Cases_on `e IN SET_OF_BAG b` THENL [
    SRW_TAC[][INSERT_INTER, SUM_IMAGE_THM] THEN
    `SET_OF_BAG b = e INSERT (SET_OF_BAG b DELETE e)`
      by (SRW_TAC[][EXTENSION] THEN METIS_TAC[IN_SET_OF_BAG])THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SRW_TAC [][SUM_IMAGE_THM] THEN
    SRW_TAC[ARITH_ss][] THEN
    SRW_TAC[][Cong SUM_IMAGE_CONG],
    SRW_TAC [][INSERT_INTER, SUM_IMAGE_THM] THEN
    `!x. x IN SET_OF_BAG b ==> x <> e` by METIS_TAC[] THEN
    SRW_TAC[][Cong SUM_IMAGE_CONG] THEN
    `b e = 0` suffices_by SRW_TAC[ARITH_ss][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [BAG_IN, BAG_INN]
  ]);

val FINITE_BAG_FOLDR_loopbag = store_thm(
  "FINITE_BAG_FOLDR_loopbag[simp]",
  ``FINITE_BAG (FOLDR (λx b. BAG_UNION (loopbag (f x)) b) acc list) <=>
    FINITE_BAG acc``,
  Induct_on `list` >> simp[]);

val mlt_loopbag_lemma = store_thm(
  "mlt_loopbag_lemma",
  ``mlt $< (FOLDR (λx b. BAG_UNION (loopbag s) b) {|0|} list)
           (BAG_IMAGE SUC (loopbag s))``,
  simp[mlt_dominates_thm1] >> qexists_tac `BAG_IMAGE SUC (loopbag s)` >>
  simp[] >> dsimp[dominates_def] >>
  qho_match_abbrev_tac
    `∀e1. BAG_IN e1 FF ⇒ ∃e2. BAG_IN e2 (loopbag s) /\ e1 < SUC e2` >>
  `∀e. BAG_IN e FF ⇒ BAG_IN e (loopbag s) ∨ e = 0`
    by (simp[Abbr`FF`] >> Induct_on `list` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> res_tac >- metis_tac[DECIDE ``x < SUC x``] >> simp[] >>
  metis_tac[loopbag_not_empty, BAG_cases, BAG_IN_BAG_INSERT]);


val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ inv_image (mlt (<) LEX (<)) (λ(m,lm,s). (loopbag s, stmt_weight s)) b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[pairTheory.LEX_DEF, MAX_SET_THM, listTheory.SUM_APPEND]
  >- (Cases_on `b` >> simp[])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- simp[rich_listTheory.FOLDR_MAP, mlt_loopbag_lemma]
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- simp[rich_listTheory.FOLDR_MAP, mlt_loopbag_lemma]
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
      Induct_on `sfx` >> simp[])
  >- (disj2_tac >> simp[listTheory.SUM_APPEND] >> rw[] >>
      Induct_on `pfx` >> simp[]) >>
  disj1_tac >> rw[] >> Induct_on `pfx` >> simp[]);

(* ----------------------------------------------------------------------
    Create an action graph from a PseudoC program.

    Function is partial to allow for possibility that actions
    parallelised underneath a Par may be touching/conflicting. If this
    happens, the result has to be NONE.
   ---------------------------------------------------------------------- *)

open monadsyntax
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = overload_on ("assert", ``OPTION_GUARD``)

(* opt_sequence : (α option) list -> α list option *)
val OPT_SEQUENCE_def = Define`
  (OPT_SEQUENCE [] = SOME []) ∧
  (OPT_SEQUENCE (h :: t) = lift2 CONS h (OPT_SEQUENCE t))
`;

val MEM_FOLDR_mlt = store_thm(
  "MEM_FOLDR_mlt",
  ``MEM e l ⇒
    mlt $< (loopbag (f e)) (FOLDR (\e a. loopbag (f e) ⊎ a) {|0|} l) ∨
    loopbag (f e) = FOLDR (\e a. loopbag (f e) ⊎ a) {|0|} l``,
  Induct_on `l` >> dsimp[] >> rpt strip_tac >> res_tac
  >- (Cases_on `loopbag (f h) = {||}` >> simp[] >>
      disj1_tac >>
      qmatch_abbrev_tac `mlt $< (loopbag (f e)) (loopbag (f h) ⊎ FF)` >>
      `mlt $< FF (loopbag (f h) ⊎ FF)` by simp[Abbr`FF`] >>
      metis_tac[relationTheory.TC_RULES]) >>
  pop_assum SUBST_ALL_TAC >> simp[]);

val pushG_def = Define`pushG v = imap (λi. v::i)`

val _ = Datatype`actionRW = Array aname int | Variable vname`

val actRWName_def = Define`
  (actRWName (Array a _) = a) ∧
  (actRWName (Variable v) = v)
`;
val _ = export_rewrites ["actRWName_def"]

val lookupRW_def = Define`
  (lookupRW m (Array a i) = lookup_array m a i) ∧
  (lookupRW m (Variable v) = lookup_v m v)
`;

val getReads_def = Define`
  (getReads m [] = SOME []) ∧
  (getReads m (ARead aname i_e :: des) =
     lift2 (λi rest. Array aname i :: rest)
           (some i. evalexpr m i_e = Int i)
           (getReads m des)) ∧
  (getReads m (VRead vname :: des) =
     OPTION_MAP (CONS (Variable vname)) (getReads m des)) ∧
  (getReads m (DValue _ :: des) = getReads m des)
`;

val mergeReads0_def = Define`
  (mergeReads0 [] acc opn vs = opn (REVERSE acc)) ∧
  (mergeReads0 (VRead _ :: ds) acc opn vs =
     mergeReads0 ds (HD vs :: acc) opn (TL vs)) ∧
  (mergeReads0 (DValue v :: ds) acc opn vs =
     mergeReads0 ds (v :: acc) opn vs) ∧
  (mergeReads0 (ARead _ _ :: ds) acc opn vs =
     mergeReads0 ds (HD vs :: acc) opn (TL vs))
`;

val mergeReads_def = Define`
  mergeReads ds opn = mergeReads0 ds [] opn
`;

val evalDexpr_def = Define`
  (evalDexpr m (DValue v) = SOME v) ∧
  (evalDexpr m (VRead vname) = SOME (lookup_v m vname)) ∧
  (evalDexpr m (ARead aname e_i) =
     do
       i <- (some i. evalexpr m e_i = Int i);
       SOME (lookup_array m aname i)
     od)
`;

val stackInc_def = Define`
  (stackInc [] = []) ∧
  (stackInc (h::t) = h + 1n :: t)
`;

val selapf_def = Define`
  selapf a lm =
    if actRWName a.write ∈ FDOM lm then
      (FST : memory # memory -> memory,
       ap1 : (memory -> memory) -> memory # memory -> memory # memory)
    else (SND, ap2)
`;

val updf_def = Define`
  updf w value m =
    case w of
      | Array a i => upd_array m a i value
      | Variable vnm => case FLOOKUP m vnm of
                          NONE => NONE
                        | SOME (Array _) => NONE
                        | SOME _ => if ∀els. value ≠ Array els then
                                      SOME(m |+ (vnm, value))
                                    else NONE
`;

val apply_action_def = Define`
  apply_action a lmm_opt =
    do
      (lm,m) <- lmm_opt;
      vs <- SOME(MAP (lookupRW (lm ⊌ m)) a.reads);
      (self,apf) <- SOME (selapf a lm);
      value <- SOME (a.expr vs);
      m' <- updf a.write value (self (lm,m));
      SOME(apf (K m') (lm,m))
    od
`;

val lift_OPTION_BIND = store_thm(
  "lift_OPTION_BIND",
  ``OPTION_BIND (OPTION_BIND v f) g =
    OPTION_BIND v (combin$C (OPTION_BIND o f) g)``,
  Cases_on `v` >> simp[]);

val updf_EQ_NONE = store_thm(
  "updf_EQ_NONE",
  ``updf w value m = NONE ⇔
     (∃a i. w = Array a i ∧ upd_array m a i value = NONE) ∨
     ∃vnm. w = Variable vnm ∧ (vnm ∉ FDOM m ∨ (∃els. value = Array els) ∨
                               vnm ∈ FDOM m ∧ ∃els. m ' vnm = Array els)``,
  Cases_on `w` >> simp[updf_def] >>
  rw[FLOOKUP_DEF] >> fs[] >> Cases_on `m ' s` >> simp[]) ;

val updarray_EQ_NONE = store_thm(
  "updarray_EQ_NONE",
  ``upd_array m a i v = NONE ⇔
    ∀vlist. FLOOKUP m a = SOME (Array vlist) ⇒ i < 0 ∨ &LENGTH vlist ≤ i``,
  `FLOOKUP m a = NONE ∨ ∃v'. FLOOKUP m a = SOME v'`
    by metis_tac[optionTheory.option_CASES] >>
  simp[upd_array_def] >> Cases_on `v'` >> simp[]);

val updf_preserves_FDOMs = store_thm(
  "updf_preserves_FDOMs",
  ``updf w value m = SOME m' ⇒ FDOM m' = FDOM m``,
  Cases_on `w` >> simp[updf_def, upd_array_def] >> rw[] >>
  simp[ABSORPTION_RWT] >>
  Cases_on `FLOOKUP m s` >> fs[] >>
  Cases_on `x` >> fs[] >> rw[] >>
  match_mp_tac ABSORPTION_RWT >>
  fs[FLOOKUP_DEF]);

val apply_action_preserves_FDOMs = store_thm(
  "apply_action_preserves_FDOMs",
  ``apply_action a (SOME(lm,gm)) = SOME (lm',gm') ⇒
    FDOM lm' = FDOM lm ∧ FDOM gm' = FDOM gm``,
  simp[apply_action_def] >>
  `selapf a lm = (FST,ap1) ∨ selapf a lm = (SND, ap2)`
    by rw[selapf_def] >>
  simp[] >> metis_tac[updf_preserves_FDOMs]);

val selapf_cases = store_thm(
  "selapf_cases",
  ``∀a lm. selapf a lm = (FST, ap1) ∨ selapf a lm = (SND, ap2)``,
  rw[selapf_def]);

val updf_preserves_array_presence_length_back = store_thm(
  "updf_preserves_array_presence_length_back",
  ``updf w value m = SOME m' ∧ FLOOKUP m' a = SOME (Array els) ⇒
    ∃els'. FLOOKUP m a = SOME (Array els') ∧ LENGTH els' = LENGTH els``,
  simp[updf_def] >> Cases_on `w` >> simp[] >| [
    simp[upd_array_def] >> Cases_on `FLOOKUP m s` >> simp[] >>
    Cases_on `x` >> simp[] >> rw[] >> fs[FLOOKUP_DEF]
    >- (rw[] >> fs[] >> rw[]) >>
    Cases_on `a = s` >> fs[FAPPLY_FUPDATE_THM] >> rw[],
    rw[FLOOKUP_DEF] >> Cases_on `m ' s` >>
    fs[] >> rw[] >> fs[] >> rw[] >> fs[] >>
    Cases_on `a = s` >> fs[FAPPLY_FUPDATE_THM]
  ]);

val updf_preserves_array_presence_length_forward = store_thm(
  "updf_preserves_array_presence_length_forward",
  ``updf w value m = SOME m' ∧ FLOOKUP m a = SOME (Array els) ⇒
    ∃els'. FLOOKUP m' a = SOME (Array els') ∧ LENGTH els' = LENGTH els``,
  simp[updf_def] >> Cases_on `w` >> simp[] >| [
    simp[upd_array_def] >> Cases_on `FLOOKUP m s` >> simp[] >>
    Cases_on `x` >> simp[] >> rw[] >> fs[FLOOKUP_DEF] >>
    Cases_on `a = s` >> fs[FAPPLY_FUPDATE_THM] >> rw[],
    rw[FLOOKUP_DEF] >> Cases_on `m ' s` >> fs[] >> rw[] >> fs[] >>
    rw[] >> fs[] >>
    Cases_on `a = s` >> fs[FAPPLY_FUPDATE_THM]
  ]);

val m_t = ``m:memory``
val m'_t = ``m':memory``

val nontouching_updfs_read_after_write = store_thm(
  "nontouching_updfs_read_after_write",
  ``updf w value m = SOME m' ∧ w ≠ rd ⇒ lookupRW m' rd = lookupRW m rd``,
  `(∃a i. w = Array a i) ∨ ∃s. w = Variable s` by (Cases_on `w` >> simp[]) >>
  `(∃b j. rd = Array b j) ∨ ∃t. rd = Variable t` by (Cases_on `rd` >> simp[]) >>
  simp[updf_def, lookupRW_def, lookup_array_def, upd_array_def, lookup_v_def] >>
  strip_tac
  >- (`FLOOKUP m a = NONE ∨ ∃v. FLOOKUP m a = SOME v`
        by (Cases_on `FLOOKUP m a` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM])
  >- (`FLOOKUP m a = NONE ∨ ∃v. FLOOKUP m a = SOME v`
        by (Cases_on `FLOOKUP m a` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM]
      >- (rw[] >>
          `0 ≤ i ∧ 0 ≤ j` by ARITH_TAC >>
          `i = &(Num i) ∧ j = &(Num j)`
            by metis_tac[integerTheory.INT_OF_NUM] >>
          `Num j < LENGTH l`
              by (fs[integerTheory.INT_NOT_LE] >>
                  metis_tac[integerTheory.INT_LT]) >>
          simp[listTheory.LUPDATE_SEM] >>
          metis_tac[integerTheory.INT_INJ])
      >- fs[]
      >- fs[])
  >- (`FLOOKUP m a = NONE ∨ ∃v. FLOOKUP m a = SOME v`
        by (Cases_on `FLOOKUP m a` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM] >>
      fs[])
  >- (`FLOOKUP m s = NONE ∨ ∃v. FLOOKUP m s = SOME v`
        by (Cases_on `FLOOKUP m s` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM] >>
      fs[] >> Cases_on `value` >> fs[])
  >- (`FLOOKUP m s = NONE ∨ ∃v. FLOOKUP m s = SOME v`
        by (Cases_on `FLOOKUP m s` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM] >>
      fs[] >> Cases_on `value` >> fs[]))

val nontouching_updfs_varread_after_write = store_thm(
  "nontouching_updfs_varread_after_write",
  ``updf w value m = SOME m' ∧ actRWName w ≠ s ⇒ m' ' s = m ' s``,
  `(∃a i. w = Array a i) ∨ ∃t. w = Variable t` by (Cases_on `w` >> simp[]) >>
  simp[updf_def, lookupRW_def, lookup_array_def, upd_array_def, lookup_v_def] >>
  strip_tac
  >- (`FLOOKUP m a = NONE ∨ ∃v. FLOOKUP m a = SOME v`
        by (Cases_on `FLOOKUP m a` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM])
  >- (`FLOOKUP m t = NONE ∨ ∃v. FLOOKUP m t = SOME v`
        by (Cases_on `FLOOKUP m t` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM]));

val lookupRW_FUNION_L = store_thm(
  "lookupRW_FUNION_L",
  ``lookupRW m1 r = lookupRW m2 r ∧ FDOM m1 = FDOM m2 ⇒
    lookupRW (m1 ⊌ m) r = lookupRW (m2 ⊌ m) r``,
  Cases_on `r` >>
  rw[lookupRW_def, lookup_array_def, lookup_v_def, FLOOKUP_DEF, FUNION_DEF] >>
  fs[]);

val lookupRW_FUNION_R = store_thm(
  "lookupRW_FUNION_R",
  ``lookupRW m1 r = lookupRW m2 r ∧ FDOM m1 = FDOM m2 ⇒
    lookupRW (m ⊌ m1) r = lookupRW (m ⊌ m2) r``,
  Cases_on `r` >>
  rw[lookupRW_def, lookup_array_def, lookup_v_def, FLOOKUP_DEF, FUNION_DEF] >>
  fs[]);


val nontouching_updfs_expreval_L = store_thm(
  "nontouching_updfs_expreval_L",
  ``¬(touches a1 a2) ∧ updf a2.write value m = SOME m' ⇒
    MAP (lookupRW (m' ⊌ m0)) a1.reads = MAP (lookupRW (m ⊌ m0)) a1.reads``,
  simp[listTheory.MAP_EQ_f] >> strip_tac >> qx_gen_tac `r` >>
  strip_tac >> match_mp_tac lookupRW_FUNION_L >>
  `r ≠ a2.write` by metis_tac[touches_def] >>
  metis_tac[nontouching_updfs_read_after_write, updf_preserves_FDOMs]);

val nontouching_updfs_expreval_R = store_thm(
  "nontouching_updfs_expreval_R",
  ``¬(touches a1 a2) ∧ updf a2.write value m = SOME m' ⇒
    MAP (lookupRW (m0 ⊌ m')) a1.reads = MAP (lookupRW (m0 ⊌ m)) a1.reads``,
  simp[listTheory.MAP_EQ_f] >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  match_mp_tac lookupRW_FUNION_R >>
  `r ≠ a2.write` by metis_tac[touches_def] >>
  metis_tac[nontouching_updfs_read_after_write, updf_preserves_FDOMs]);

val FLOOKUP_memory_cases = prove(
  ``!x: value option.
      x = NONE ∨ (∃i. x = SOME (Int i)) ∨ (∃r. x = SOME (Real r)) ∨
      (∃vl. x = SOME (Array vl)) ∨ (∃b. x = SOME (Bool b)) ∨
      x = SOME Error``,
  metis_tac[optionTheory.option_CASES, TypeBase.nchotomy_of ``:value``]);

fun findOptionCases (g as (asl,w)) =
    case bvk_find_term
           (fn (bvs,t) => optionSyntax.is_option (type_of t) andalso
                          HOLset.isEmpty
                            (HOLset.intersection(
                                HOLset.fromList Term.compare bvs,
                                FVL [t] empty_tmset)) andalso
                          not (optionSyntax.is_none t) andalso
                          not (optionSyntax.is_some t)
                          andalso
                          not (can (find_term is_abs) t))
           (fn x => x) w
    of
       NONE => NO_TAC g
     | SOME t => Cases_on `^t` g

val NEQ_SOME = prove(
  ``x = NONE ⇒ x ≠ SOME y``,
  simp[])

val selapf_t = ``selapf a1 m``
fun resolve_selapfs (g as (asl,w)) = let
  val sel_t = find_term (can (match_term selapf_t)) w
in
  case List.find (fn t => aconv (rator (lhs t)) (rator sel_t)) asl of
      NONE => NO_TAC
    | SOME asm_t => SUBGOAL_THEN (mk_eq(sel_t, lhs asm_t)) ASSUME_TAC >| [
                      REWRITE_TAC [selapf_def] >> AP_THM_TAC >> AP_THM_TAC >>
                      AP_TERM_TAC >> AP_TERM_TAC >> RES_TAC,
                      ALL_TAC
                    ]
end g

val flookupmem_t = ``FLOOKUP (m:memory) s``
val matches_flookupmem = can (match_term flookupmem_t)
fun flookupmem_tac (g as (asl,w)) = let
  val t = find_term matches_flookupmem w
in
  STRIP_ASSUME_TAC (SPEC t FLOOKUP_memory_cases) g
end

fun asmflookupmem_tac (g as (asl,w)) = let
  fun flmem_subt t =
      bvk_find_term (fn (bvs,t) => null bvs andalso matches_flookupmem t)
                    (fn x => x) t
in
  case get_first flmem_subt asl of
      NONE => NO_TAC g
    | SOME t => STRIP_ASSUME_TAC (SPEC t FLOOKUP_memory_cases) g
end

fun eqNONE_tac (g as (asl,w)) = let
  val asm_eqNONE_t =
      valOf (List.find (fn t => is_eq t andalso
                                type_of (rhs t) = ``:memory option`` andalso
                                optionSyntax.is_none (rhs t))
                       asl) handle Option => raise mk_HOL_ERR "" "" ""
  val upd_t = #1 (strip_comb (lhs asm_eqNONE_t))
  val upd_name = #1 (dest_var upd_t)
  val other_name = if upd_name = "A1U" then "A2U" else "A1U"
  val rearrange_tac =
      case List.find (fn t => is_eq t andalso
                              type_of (rhs t) = ``:memory option`` andalso
                              optionSyntax.is_some (rhs t) andalso
                              aconv upd_t (#1 (strip_comb (lhs t)))) asl
       of
          NONE => ALL_TAC
        | SOME t => UNDISCH_TAC t >> CONV_TAC (REWR_CONV IMP_DISJ_THM) >>
                    disj1_tac >> match_mp_tac NEQ_SOME
  val flookup_case =
    gen_tac >>
    rpt strip_tac >>
    qunabbrev_tac [QUOTE other_name] >> fs[] >>
    first_x_assum (fn th10 => let
      val th1 =
          assert (can (match_term ``updf WW VV MM = SOME MM'`` o concl))
                 th10
    in
      pop_assum (fn th2 =>
        let
          val th =
              MATCH_MP (GEN_ALL updf_preserves_array_presence_length_forward)
                       (CONJ th1 th2)
              handle HOL_ERR _ =>
              MATCH_MP (GEN_ALL updf_preserves_array_presence_length_back)
                       (CONJ th1 th2)
        in
          STRIP_ASSUME_TAC th
        end)
    end) >>
    pop_assum (fn th1 =>
      pop_assum (fn th2 =>
        first_x_assum (fn imp =>
          mp_tac (SPEC (rand (rand (rhs (concl th2)))) imp)) >>
        assume_tac th2) >>
      assume_tac th1) >> simp[]
  val expr_case =
    disj2_tac >> disj1_tac >>
    qpat_assum `XX = Array ZZ:value`
      (fn th => EXISTS_TAC (rand (rhs (concl th))) THEN
                REWRITE_TAC [SYM th]) >> AP_TERM_TAC >>
    simp[listTheory.MAP_EQ_f] >> rpt strip_tac >>
    (match_mp_tac lookupRW_FUNION_L ORELSE
     match_mp_tac lookupRW_FUNION_R) >> ASM_REWRITE_TAC [] >>
    qunabbrev_tac [QUOTE other_name] >> fs[] >>
    metis_tac[nontouching_updfs_read_after_write, touches_def]
  val vararray_case =
    disj2_tac >> qunabbrev_tac [QUOTE other_name] >> fs[] >>
    qpat_assum `vv ∈ FDOM (mm:memory)`
      (fn th => let
         val m_t = rand (rand (concl th))
       in
         assume_tac th >>
         qpat_assum `updf ww vv ^m_t = SOME mm'`
           (fn th => Cases_on `^(hd (#2 (strip_comb (lhs (concl th)))))` >>
                     mp_tac th)
       end) >> simp[updf_def, upd_array_def] >>
    flookupmem_tac >> simp[] >> rw[] >>
    rw[FAPPLY_FUPDATE_THM] >>
    fs[touches_def, FAPPLY_FUPDATE_THM, FLOOKUP_DEF] >>
    full_simp_tac (srw_ss() ++ boolSimps.COND_elim_ss) [] >> fs[]
  val None_subtac = flookup_case ORELSE expr_case ORELSE vararray_case
in
  rearrange_tac >>
  RES_TAC >>
  qunabbrev_tac [QUOTE upd_name] >>
  fs[updf_EQ_NONE, updarray_EQ_NONE] >>
  None_subtac
end g

val updf_VAR_SOME_EQN = store_thm(
  "updf_VAR_SOME_EQN",
  ``updf (Variable s) v m = SOME m' ⇔
    (∀es. v ≠ Array es) ∧ s ∈ FDOM m ∧ (∀es. m ' s ≠ Array es) ∧
    m' = m |+ (s,v)``,
  simp[updf_def] >> flookupmem_tac >> simp[] >> fs[FLOOKUP_DEF] >>
  metis_tac[]);

val updf_writes_commute = store_thm(
  "updf_writes_commute",
  ``w1 ≠ w2 ∧
    updf w1 v1 m0 = SOME m11 ∧ updf w2 v2 m11 = SOME m12 ∧
    updf w2 v2 m0 = SOME m21 ∧ updf w1 v1 m21 = SOME m22 ⇒
    m12 = m22``,
  Cases_on `w1` >> Cases_on `w2` >| [
    simp[updf_def, upd_array_def] >>
    rpt (flookupmem_tac >> simp[]) >> rw[] >>
    fs[FLOOKUP_DEF, FAPPLY_FUPDATE_THM, integerTheory.INT_NOT_LE,
       integerTheory.INT_NOT_LT] >|
    [
      dsimp[fmap_EXT, FAPPLY_FUPDATE_THM] >> conj_tac
      >- (simp[EXTENSION] >> metis_tac[]) >>
      rw[],
      rw[] >> dsimp[fmap_EXT, FAPPLY_FUPDATE_THM] >> csimp[] >>
      qmatch_rename_tac `
        LUPDATE v2 (Num j) (LUPDATE v1 (Num i) a1) =
        LUPDATE v1 (Num i) (LUPDATE v2 (Num j) a2)` [] >>
      `a1 = a2` by fs[] >> rw[] >>
      simp[listTheory.LIST_EQ_REWRITE, listTheory.LUPDATE_SEM] >>
      `Num i ≠ Num j`
        by metis_tac[integerTheory.INT_INJ, integerTheory.INT_OF_NUM] >>
      rw[] >> fs[],
      qmatch_rename_tac `
        m0 |+ (s, Array (LUPDATE v1 (Num i) a1))
           |+ (t, Array (LUPDATE v2 (Num j) a2)) = XX` ["XX"] >>
      reverse (Cases_on `s = t`)
      >- (fs[] >> dsimp[fmap_EXT, FAPPLY_FUPDATE_THM] >>
          rw[EXTENSION] >> metis_tac[]) >>
      fs[] >> rw[] >> dsimp[fmap_EXT, FAPPLY_FUPDATE_THM] >> csimp[] >>
      `Num i ≠ Num j`
        by metis_tac[integerTheory.INT_INJ, integerTheory.INT_OF_NUM] >>
      simp[listTheory.LIST_EQ_REWRITE, listTheory.LUPDATE_SEM] >>
      rw[] >> fs[]
    ],

    simp[SPEC ``Array a i`` updf_def, upd_array_def,
         updf_VAR_SOME_EQN] >>
    rpt (flookupmem_tac >> simp[]) >> fs[FLOOKUP_DEF] >>
    rpt strip_tac >> rw[] >>
    qmatch_rename_tac `m0 |+ (s, XX) |+ (t, YY) = ZZ`
      ["XX", "YY", "ZZ"] >>
    `s ≠ t` by (strip_tac >> fs[]) >>
    fs[FAPPLY_FUPDATE_THM] >> metis_tac[FUPDATE_COMMUTES],

    simp[SPEC ``Array a i`` updf_def, upd_array_def,
         updf_VAR_SOME_EQN] >>
    rpt (flookupmem_tac >> simp[]) >> fs[FLOOKUP_DEF] >>
    rpt strip_tac >> rw[] >>
    qmatch_rename_tac `m0 |+ (s, XX) |+ (t, YY) = ZZ`
      ["XX", "YY", "ZZ"] >>
    `s ≠ t` by (strip_tac >> fs[]) >>
    fs[FAPPLY_FUPDATE_THM] >> metis_tac[FUPDATE_COMMUTES],

    simp[updf_VAR_SOME_EQN] >> rpt strip_tac >>
    simp[FUPDATE_COMMUTES]
  ])

fun ae_equate_tac anm (g as (asl,w)) = let
  fun ae_term t = let
    val (f, xs) = strip_comb t
  in
    #1 (dest_var f) = "ae" andalso length xs = 2 andalso
    #1 (dest_var (hd xs)) = anm
  end handle HOL_ERR _ => false
  fun get_ae_term t =
      bvk_find_term (fn (_,t) => ae_term t) (fn x => x) t
  val (t1,t2) = case List.mapPartial get_ae_term asl of
                    [t1,t2] => (t1,t2)
                  | _ => raise mk_HOL_ERR "" "ae_equate_tac"
                               ("Don't have 2 ae-terms for "^anm)
in
  SUBGOAL_THEN (mk_eq(t1,t2)) SUBST_ALL_TAC THENL [
    qunabbrev_tac `ae` >> fs[] >>
    metis_tac[nontouching_updfs_expreval_R, touches_SYM,
              nontouching_updfs_expreval_L],
    ALL_TAC
  ]
end g

val success_case =
  rpt (qpat_assum `selapf xx yy = zz` kall_tac) >>
  rpt (first_x_assum (kall_tac o assert (is_forall o concl))) >>
  map_every qunabbrev_tac [`A1U`, `A2U`] >> fs[] >>
  qabbrev_tac `
    ae = λa:(value,actionRW,α)action m. a.expr (MAP (lookupRW m) a.reads)
  ` >> fs[] >>
  ae_equate_tac "a1" >> ae_equate_tac "a2" >> fs[] >>
  metis_tac[updf_writes_commute, touches_def]


val apply_action_commutes = store_thm(
  "apply_action_commutes",
  ``¬(a1:(value,actionRW,α)action ∼ₜ a2:(value,actionRW,α)action) ⇒
    (apply_action a2 (apply_action a1 m) =
     apply_action a1 (apply_action a2 m))``,
  strip_tac >>
  `m = NONE ∨ ∃lm gm. m = SOME(lm,gm)`
     by metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES] >>
  simp[apply_action_def, lift_OPTION_BIND, combinTheory.o_ABS_R,
       pairTheory.o_UNCURRY_R, pairTheory.C_UNCURRY_L,
       combinTheory.C_ABS_L] >>
  qabbrev_tac `A1U = λm. updf a1.write (a1.expr (MAP (lookupRW m) a1.reads))` >>
  qabbrev_tac `A2U = λm. updf a2.write (a2.expr (MAP (lookupRW m) a2.reads))` >>
  simp[] >>
  `(∀rm m m'. A1U rm m = SOME m' ⇒ FDOM m' = FDOM m) ∧
   (∀rm m m'. A2U rm m = SOME m' ⇒ FDOM m' = FDOM m)`
     by (simp[Abbr`A1U`, Abbr`A2U`] >> metis_tac[updf_preserves_FDOMs]) >>
  Q.ISPECL_THEN [`a1`, `lm`] strip_assume_tac selapf_cases >>
  Q.ISPECL_THEN [`a2`, `lm`] strip_assume_tac selapf_cases >>
  fs[] >> rw[] >>
  rpt (findOptionCases >> simp[]) >>
  rpt (resolve_selapfs >> simp[]) >> TRY eqNONE_tac >>
  rpt (findOptionCases >> simp[]) >> TRY eqNONE_tac >>
  success_case)

val commutes_lemma = prove(
  ``∀a1 a2 s.
      ¬(a1 ∼ₜ a2) ∧ a1.iter ≠ a2.iter ⇒
      apply_action a2 (apply_action a1 s) =
      apply_action a1 (apply_action a2 s)``,
  simp[apply_action_commutes]);

val pcg_eval_def = Define`
  pcg_eval g s = gEVAL apply_action s g
`;

val pcg_eval_thm = save_thm(
  "pcg_eval_thm",
  MATCH_MP gEVAL_thm commutes_lemma
           |> REWRITE_RULE [GSYM pcg_eval_def]);

val pop_scope_def = Define`
  pop_scope old nested new =
    DRESTRICT new (COMPL (FDOM nested)) ⊌ old
`;

val graphOf_def = tDefine "graphOf" `

  (graphOf i lm m (IfStmt g t e) =
     case evalexpr (lm ⊌ m) g of
       | Bool T => graphOf i lm m t
       | Bool F => graphOf i lm m e
       | _ => NONE) ∧

  (graphOf i lm0 m0 (ForLoop vnm d body) =
     do
       dvs <- dvalues (lm0 ⊌ m0) d;
       graphOf i lm0 m0 (Seq (MAP (λv. (FEMPTY |+ (vnm,v),body)) dvs))
     od) ∧

  (graphOf i lm0 m0 (Seq cmds) =
     case cmds of
       | [] => SOME (lm0, m0, emptyG)
       | (lm,c) :: rest =>
         do
           (lm1, m1, G1) <- graphOf i (lm ⊌ lm0) m0 c;
           lm1' <- SOME (pop_scope lm0 lm lm1);
           (lm2, m2, G2) <- graphOf (stackInc i) lm1' m1 (Seq rest);
           SOME(lm2,m2,merge_graph G1 G2)
         od) ∧

  (graphOf i lm0 m0 (ParLoop vnm d body) =
     do
       dvs <- dvalues (lm0 ⊌ m0) d;
       graphOf i lm0 m0 (Par (MAP (λv. (FEMPTY |+ (vnm,v), body)) dvs))
     od) ∧

  (graphOf i lm0 m0 (Par cmds) =
     do
       ps0 <-
         OPT_SEQUENCE
           (MAP
              (λ(lm,c). OPTION_MAP (SND o SND) (graphOf i (lm ⊌ lm0) m0 c))
              cmds);
       ps <- SOME (GENLIST (λn. pushG n (EL n ps0)) (LENGTH ps0));
       assert(∀i j. i < j ∧ j < LENGTH ps ⇒ ¬gtouches (EL i ps) (EL j ps));
       g <- SOME (FOLDR merge_graph emptyG ps);
       (lm,m) <- pcg_eval g (SOME(lm0,m0));
       SOME(lm, m, merge_graph (pushG (LENGTH ps0) G0) g)
     od) ∧

  (graphOf iter lm0 m0 (Assign w ds opn) =
     do (aname,i_e) <- SOME w;
        i <- (some i. evalexpr (lm0 ⊌ m0) i_e = Int i);
        rds <- getReads (lm0 ⊌ m0) ds;
        a <- SOME <| write := Array aname i;
                     reads := rds;
                     expr := mergeReads ds opn;
                     iter := iter |> ;
        rvs <- OPT_SEQUENCE (MAP (evalDexpr (lm0 ⊌ m0)) ds);
        m' <- upd_array m0 aname i (opn rvs);
        SOME(lm0, m', a ⊕ emptyG)
     od)

` (WF_REL_TAC
     `inv_image (mlt (<) LEX (<)) (λ(i,lm,m,s). (loopbag s, stmt_weight s))` >>
   simp[WF_mlt1, rich_listTheory.FOLDR_MAP, mlt_loopbag_lemma] >>
   rpt strip_tac
   >- (imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `SND` mp_tac) >>
       rw[] >> simp[] >> pop_assum kall_tac >> pop_assum mp_tac >>
       map_every qid_spec_tac [`lm`, `c`] >> Induct_on `cmds` >> dsimp[] >>
       rpt strip_tac >> res_tac >> decide_tac))


(*val graphOf_correct = store_thm(
  "graphOf_correct",
  ``...``
*)



val _ = export_theory();
