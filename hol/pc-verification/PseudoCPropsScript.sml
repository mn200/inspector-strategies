open HolKernel Parse boolLib bossLib;

open lcsymtacs

open bagTheory
open PseudoCTheory
open actionTheory
open pred_setTheory finite_mapTheory
open intLib
open pairTheory listTheory rich_listTheory
open boolSimps
open indexedListsTheory

val _ = new_theory "PseudoCProps";

val expr_weight_def = Define`
  (expr_weight (Value v) = 0:num) ∧
  (expr_weight e = 1)
`;
val _ = export_rewrites ["expr_weight_def"]

val dexpr_weight_def = Define`
  (dexpr_weight (DValue v) = 0:num) ∧
  (dexpr_weight (DARead v e) = 1 + expr_weight e) ∧
  (dexpr_weight (DVRead v) = 1)
`;
val _ = export_rewrites ["dexpr_weight_def"]

val stmt_weight_def = tDefine "stmt_weight" `
  (stmt_weight Abort = 0) ∧
  (stmt_weight Done = 0) ∧
  (stmt_weight (Assign w ds v) =
     1 + ew (SND w) + SUM (MAP dw ds)) ∧
  (stmt_weight (AssignVar v ds vf) = 1 + SUM (MAP dw ds)) ∧
  (stmt_weight (Malloc v d value) = 1) ∧
  (stmt_weight (IfStmt g t e) = MAX (stmt_weight t) (stmt_weight e) + 3) ∧
  (stmt_weight (ForLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (ParLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (Seq stmts) = SUM (MAP stmt_weight stmts) + LENGTH stmts) ∧
  (stmt_weight (Par stmts) =
    SUM (MAP stmt_weight stmts) + 1 + LENGTH stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["stmt_weight_def"]


val seq_count_def = tDefine "seq_count" `
  (seq_count (Seq cs) = SUM (MAP seq_count cs) + 1) ∧
  (seq_count (Par cs) = SUM (MAP seq_count cs) + 1) ∧
  (seq_count (ParLoop v d s) = seq_count s) ∧
  (seq_count (ForLoop v d s) = seq_count s) ∧
  (seq_count (IfStmt g t e) = seq_count t + seq_count e) ∧
  (seq_count _ = 0)
`
  (WF_REL_TAC `measure stmt_size` >> simp[] >> Induct >> simp[] >>
   rpt strip_tac >> simp[stmt_size_def] >> res_tac >> simp[])
val _ = export_rewrites ["seq_count_def"]

val loopbag_def = tDefine "loopbag" `
  (loopbag Abort = {| |}) ∧
  (loopbag Done = {| |}) ∧
  (loopbag (Assign w ds v) = {| |}) ∧
  (loopbag (AssignVar v ds vf) = {| |}) ∧
  (loopbag (Malloc v d value) = {| |}) ∧
  (loopbag (IfStmt g t e) = BAG_UNION (loopbag t) (loopbag e)) ∧
  (loopbag (ForLoop v d s) = if loopbag s = {||} then {|1|}
                             else BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (ParLoop v d s) = if loopbag s = {||} then {|1|}
                             else BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (Seq stmts) =
     FOLDR (λms b. BAG_UNION (loopbag ms) b) {||} stmts) ∧
  (loopbag (Par stmts) =
     FOLDR (λms b. BAG_UNION (loopbag ms) b) {||} stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["loopbag_def"]

val FINITE_loopbag = store_thm(
  "FINITE_loopbag[simp]",
  ``∀s. FINITE_BAG (loopbag s)``,
  ho_match_mp_tac (theorem "loopbag_ind") >>
  simp[] >> reverse (rpt conj_tac)
  >- (Induct >> simp[]) >> rw[]);

val MAX_PLUS = store_thm(
  "MAX_PLUS",
  ``MAX x y + z = MAX (x + z) (y + z)``,
  rw[arithmeticTheory.MAX_DEF]);

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
  ``loopbag s ≠ {||} ⇒
    mlt $< (FOLDR (λx b. BAG_UNION (loopbag s) b) {||} list)
           (BAG_IMAGE SUC (loopbag s))``,
  simp[mlt_dominates_thm1] >> strip_tac >>
  qexists_tac `BAG_IMAGE SUC (loopbag s)` >>
  simp[] >> dsimp[dominates_def] >>
  qho_match_abbrev_tac
    `∀e1. BAG_IN e1 FF ⇒ ∃e2. BAG_IN e2 (loopbag s) /\ e1 < SUC e2` >>
  `list ≠ [] ⇒ ∀e. BAG_IN e FF ⇒ BAG_IN e (loopbag s)`
    by (simp[Abbr`FF`] >> Induct_on `list` >> simp[] >>
        Cases_on `list` >> fs[] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `list` >> fs[] >- fs[Abbr`FF`] >>
  res_tac >> metis_tac[DECIDE ``x < SUC x``])

val FORALL_domain = store_thm(
  "FORALL_domain",
  ``(∀d. P d) ⇔ ∀e1 e2. P (D e1 e2)``,
  simp[EQ_IMP_THM] >> strip_tac >> Cases >> simp[]);

val loopbag_ssubst = store_thm(
  "loopbag_ssubst[simp]",
  ``loopbag (ssubst vnm value s) = loopbag s``,
  qid_spec_tac `s` >> ho_match_mp_tac stmt_induction >>
  asm_simp_tac (srw_ss() ++ COND_elim_ss)
    [ssubst_def, FORALL_domain] >>
  simp[FOLDR_MAP,
      Cong (SPEC_ALL
              (REWRITE_RULE [GSYM AND_IMP_INTRO] FOLDR_CONG))] >>
  metis_tac[]);

val _ = overload_on (
  "evalR",
  ``inv_image (mlt (<) LEX (<) LEX (<))
      (λ(m:memory,s). (loopbag s, stmt_weight dexpr_weight expr_weight s,
                       seq_count s))``
)

val WF_evalR = store_thm(
  "WF_evalR",
  ``WF evalR``,
  simp[WF_LEX, relationTheory.WF_TC_EQN,
       relationTheory.WF_inv_image, bagTheory.WF_mlt1]);

val WF_eval_induction =
    relationTheory.WF_INDUCTION_THM
      |> C MATCH_MP WF_evalR
      |> SIMP_RULE (srw_ss()) [FORALL_PROD, LEX_DEF]
      |> Q.SPEC `λms. Q (FST ms) (SND ms)`
      |> SIMP_RULE (srw_ss()) []
      |> Q.GEN `Q`

val mlt_FINITE_BAG = store_thm(
  "mlt_FINITE_BAG",
  ``∀s1 s2. mlt R s1 s2 ⇒ FINITE_BAG s1 ∧ FINITE_BAG s2``,
  Induct_on `TC` >> simp[mlt1_def]);

val mlt_EMPTY_BAG = store_thm(
  "mlt_EMPTY_BAG[simp]",
  ``mlt R {||} s ⇔ FINITE_BAG s ∧ s ≠ {||}``,
  eq_tac
  >- (`∀s1 s2. mlt R s1 s2 ⇒ s1 = {||} ⇒ FINITE_BAG s2 ∧ s2 ≠ {||}`
        suffices_by metis_tac[] >>
      Induct_on `TC` >> simp[] >> rpt strip_tac >>
      fs[mlt1_def] >> imp_res_tac mlt_FINITE_BAG) >>
  `∀s. FINITE_BAG s ⇒ s ≠ {||} ⇒ mlt R {||} s`
    suffices_by metis_tac[] >>
  Induct_on `FINITE_BAG` >> simp[] >> qx_gen_tac `b` >>
  strip_tac >> qx_gen_tac `e` >> Cases_on `b = {||}` >> fs[]
  >- (match_mp_tac relationTheory.TC_SUBSET >> simp[mlt1_def]) >>
  `mlt R b (BAG_INSERT e b)`
    by (match_mp_tac relationTheory.TC_SUBSET >>
        simp[mlt1_def] >> map_every qexists_tac [`e`, `{||}`, `b`] >>
        simp[] >> simp[BAG_EXTENSION, BAG_INN, BAG_INSERT, BAG_UNION,
                       EMPTY_BAG] >>
        map_every qx_gen_tac [`m`, `d`] >> Cases_on `d = e` >> simp[]) >>
  metis_tac[relationTheory.TC_RULES]);

val FOLDR_KI = store_thm(
  "FOLDR_KI[simp]",
  ``FOLDR (\e a. a) acc list = acc``,
  Induct_on `list` >> simp[]);

val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ evalR b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[LEX_DEF, MAX_SET_THM, SUM_APPEND]
  >- (Induct_on `pfx` >> simp[])
  >- (Induct_on `pfx` >> simp[])
  >- (Induct_on `pfx` >> simp[])
  >- (metis_tac[])
  >- (Cases_on `b` >> simp[MAX_PLUS])
  >- (metis_tac[])
  >- (Cases_on `e` >> fs[isValue_def])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (rw[] >> simp[FOLDR_MAP, mlt_loopbag_lemma])
  >- (rw[])
  >- (rw[] >> simp[FOLDR_MAP, mlt_loopbag_lemma])
  >- (rw[])
  >- (disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
      Induct_on `sfx` >> simp[])
  >- (disj2_tac >> rw[] >> Induct_on `pfx` >> simp[])
  >- (disj2_tac >> rw[] >> Induct_on `pfx` >> simp[])
  >- (metis_tac[])
  >- (metis_tac[]));

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
    mlt $< (loopbag (f e)) (FOLDR (\e a. loopbag (f e) ⊎ a) {||} l) ∨
    loopbag (f e) = FOLDR (\e a. loopbag (f e) ⊎ a) {||} l``,
  Induct_on `l` >> dsimp[] >> rpt strip_tac >> res_tac
  >- (Cases_on `loopbag (f h) = {||}` >> simp[] >>
      disj1_tac >>
      qmatch_abbrev_tac `mlt $< (loopbag (f e)) (loopbag (f h) ⊎ FF)` >>
      `mlt $< FF (loopbag (f h) ⊎ FF)` by simp[Abbr`FF`] >>
      metis_tac[relationTheory.TC_RULES]) >>
  pop_assum SUBST_ALL_TAC >> simp[]);

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
  (getReads m (DARead aname i_e :: des) =
     lift2 (λi rest. Array aname i :: rest)
           (some i. evalexpr m i_e = Int i)
           (getReads m des)) ∧
  (getReads m (DVRead vname :: des) =
     OPTION_MAP (CONS (Variable vname)) (getReads m des)) ∧
  (getReads m (DValue _ :: des) = getReads m des)
`;

val mergeReads0_def = Define`
  (mergeReads0 [] acc opn vs = opn (REVERSE acc)) ∧
  (mergeReads0 (DVRead _ :: ds) acc opn vs =
     mergeReads0 ds (HD vs :: acc) opn (TL vs)) ∧
  (mergeReads0 (DValue v :: ds) acc opn vs =
     mergeReads0 ds (v :: acc) opn vs) ∧
  (mergeReads0 (DARead _ _ :: ds) acc opn vs =
     mergeReads0 ds (HD vs :: acc) opn (TL vs))
`;

val mergeReads_def = Define`
  mergeReads ds opn = mergeReads0 ds [] opn
`;

val evalDexpr_def = Define`
  (evalDexpr m (DValue v) = SOME v) ∧
  (evalDexpr m (DVRead vname) = SOME (lookup_v m vname)) ∧
  (evalDexpr m (DARead aname e_i) =
     do
       i <- (some i. evalexpr m e_i = Int i);
       SOME (lookup_array m aname i)
     od)
`;

val updLast_def = Define`
  (updLast f [] = []) /\
  (updLast f [h] = [f h]) /\
  (updLast f (h::t) = h::updLast f t)
`;
val _ = export_rewrites ["updLast_def"]

val updLast_EQ_NIL = store_thm(
  "updLast_EQ_NIL[simp]",
  ``(updLast f x = [] ⇔ x = []) ∧
    ([] = updLast f x ⇔ x = [])``,
  Cases_on `x` >> simp[] >> Cases_on `t` >> simp[]);

val updLast_FRONT_LAST = store_thm(
  "updLast_FRONT_LAST",
  ``updLast f l = if l = [] then []
                  else FRONT l ++ [f (LAST l)]``,
  Induct_on `l` >> simp[] >> Cases_on `l` >> simp[]);

val updf_def = Define`
  updf w value m =
    case w of
      | Array a i => upd_array m a i value
      | Variable vnm => upd_var m vnm value
`;

val apply_action_def = Define`
  apply_action a m_opt =
    case a.writes of
        [] => m_opt
      | (w::_) =>
        do
          m <- m_opt;
          vs <- SOME(MAP (lookupRW m) a.reads);
          value <- SOME (a.data vs);
          updf w value m
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
     ∃vnm. w = Variable vnm ∧ upd_var m vnm value = NONE``,
  Cases_on `w` >> simp[updf_def]);

val upd_var_EQ_NONE = store_thm(
  "upd_var_EQ_NONE",
  ``upd_var m vnm v = NONE ⇔
      vnm ∉ FDOM m ∨ (∃els. m ' vnm = Array els) ∨
      v = Error ∨ ∃els. v = Array els``,
  rw[upd_var_def] >> metis_tac[]);

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
  Cases_on `w` >> simp[updf_def, upd_array_def, upd_var_def] >> rw[] >>
  simp[ABSORPTION_RWT] >>
  Cases_on `FLOOKUP m s` >> fs[] >>
  Cases_on `x` >> fs[] >> rw[] >>
  match_mp_tac ABSORPTION_RWT >>
  fs[FLOOKUP_DEF]);

val apply_action_preserves_FDOMs = store_thm(
  "apply_action_preserves_FDOMs",
  ``apply_action a (SOME m) = SOME m' ⇒ FDOM m' = FDOM m``,
  simp[apply_action_def] >> Cases_on `a.writes` >> simp[] >>
  metis_tac[updf_preserves_FDOMs]);

val updf_preserves_array_presence_length_back = store_thm(
  "updf_preserves_array_presence_length_back",
  ``updf w value m = SOME m' ∧ FLOOKUP m' a = SOME (Array els) ⇒
    ∃els'. FLOOKUP m a = SOME (Array els') ∧ LENGTH els' = LENGTH els``,
  simp[updf_def] >> Cases_on `w` >> simp[] >| [
    simp[upd_array_def] >> Cases_on `FLOOKUP m s` >> simp[] >>
    Cases_on `x` >> simp[] >> rw[] >> fs[FLOOKUP_DEF]
    >- (rw[] >> fs[] >> rw[]) >>
    Cases_on `a = s` >> fs[FAPPLY_FUPDATE_THM] >> rw[],
    rw[FLOOKUP_DEF, upd_var_def] >> fs[] >> rw[] >> fs[] >>
    fs[FAPPLY_FUPDATE_THM] >> pop_assum mp_tac >> rw[]
  ]);

val updf_preserves_array_presence_length_forward = store_thm(
  "updf_preserves_array_presence_length_forward",
  ``updf w value m = SOME m' ∧ FLOOKUP m a = SOME (Array els) ⇒
    ∃els'. FLOOKUP m' a = SOME (Array els') ∧ LENGTH els' = LENGTH els``,
  simp[updf_def] >> Cases_on `w` >> simp[] >| [
    simp[upd_array_def] >> Cases_on `FLOOKUP m s` >> simp[] >>
    Cases_on `x` >> simp[] >> rw[] >> fs[FLOOKUP_DEF] >>
    Cases_on `a = s` >> fs[FAPPLY_FUPDATE_THM] >> rw[],
    rw[FLOOKUP_DEF, upd_var_def] >> simp[FAPPLY_FUPDATE_THM] >> rw[] >> fs[]
  ])

val m_t = ``m:memory``
val m'_t = ``m':memory``

val nontouching_updfs_read_after_writes = store_thm(
  "nontouching_updfs_read_after_writes",
  ``updf w value m = SOME m' ∧ w ≠ rd ⇒ lookupRW m' rd = lookupRW m rd``,
  `(∃a i. w = Array a i) ∨ ∃s. w = Variable s` by (Cases_on `w` >> simp[]) >>
  `(∃b j. rd = Array b j) ∨ ∃t. rd = Variable t` by (Cases_on `rd` >> simp[]) >>
  simp[updf_def, lookupRW_def, lookup_array_def, upd_array_def, lookup_v_def,
       upd_var_def] >>
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
          simp[LUPDATE_SEM] >>
          metis_tac[integerTheory.INT_INJ])
      >- fs[]
      >- fs[])
  >- (`FLOOKUP m a = NONE ∨ ∃v. FLOOKUP m a = SOME v`
        by (Cases_on `FLOOKUP m a` >> simp[]) >> fs[] >>
      Cases_on `v` >> fs[FLOOKUP_DEF] >> rw[FAPPLY_FUPDATE_THM] >>
      fs[])
  >- (rw[FAPPLY_FUPDATE_THM, FLOOKUP_DEF] >>
      TRY (Cases_on `value` >> fs[]) >>
      TRY (Cases_on `m ' b` >> fs[]))
  >- rw[FAPPLY_FUPDATE_THM, FLOOKUP_DEF]);

val nontouching_updfs_expreval = store_thm(
  "nontouching_updfs_expreval",
  ``¬(touches a1 a2) ∧ a2.writes = w::rest ∧ updf w value m = SOME m' ⇒
    MAP (lookupRW m') a1.reads = MAP (lookupRW m) a1.reads``,
  simp[MAP_EQ_f] >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  `r ≠ w` by metis_tac[touches_def, MEM] >>
  metis_tac[nontouching_updfs_read_after_writes]);

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

val flookupmem_t = ``FLOOKUP (m:memory) s``
val matches_flookupmem = can (match_term flookupmem_t)
fun flookupmem_tac (g as (asl,w)) = let
  val t = find_term matches_flookupmem w
in
  STRIP_ASSUME_TAC (SPEC t FLOOKUP_memory_cases) g
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
  val expr_error_case =
    qpat_assum `XX = Error` (SUBST1_TAC o SYM) >>
    disj2_tac >> disj2_tac >> disj1_tac >> AP_TERM_TAC >>
    simp[MAP_EQ_f] >> rpt strip_tac >>
    qunabbrev_tac [QUOTE other_name] >> fs[] >>
    metis_tac[nontouching_updfs_read_after_writes, touches_def]
  val expr_case =
    rpt disj2_tac >>
    qpat_assum `XX = Array ZZ:value`
      (fn th => EXISTS_TAC (rand (rhs (concl th))) THEN
                REWRITE_TAC [SYM th]) >> AP_TERM_TAC >>
    simp[MAP_EQ_f] >> rpt strip_tac >>
    qunabbrev_tac [QUOTE other_name] >> fs[] >>
    metis_tac[nontouching_updfs_read_after_writes, touches_def]
  val vararray_case =
    qunabbrev_tac [QUOTE other_name] >> fs[] >>
    qpat_assum `mm : memory ' vv = Array eee` assume_tac >>
    metis_tac[SIMP_RULE (srw_ss() ++ COND_elim_ss) [FLOOKUP_DEF]
                        (CONJ updf_preserves_array_presence_length_back
                              updf_preserves_array_presence_length_forward)]

  val None_subtac = flookup_case ORELSE expr_error_case ORELSE
                    vararray_case ORELSE expr_case
in
  rearrange_tac >>
  RES_TAC >>
  qunabbrev_tac [QUOTE upd_name] >>
  fs[updf_EQ_NONE, updarray_EQ_NONE, upd_var_EQ_NONE] >>
  None_subtac
end g

val updf_VAR_SOME_EQN = store_thm(
  "updf_VAR_SOME_EQN",
  ``updf (Variable s) v m = SOME m' ⇔
    (∀es. v ≠ Array es) ∧ s ∈ FDOM m ∧ (∀es. m ' s ≠ Array es) ∧ v ≠ Error ∧
    m' = m |+ (s,v)``,
  simp[updf_def, upd_var_def] >> metis_tac[]);

fun disjneq_search (g as (asl,w)) = let
  val ds = strip_disj w
  fun is_neq t = is_eq (dest_neg t) handle HOL_ERR _ => false
in
  case List.find is_neq ds of
      NONE => NO_TAC
    | SOME d => ASM_CASES_TAC (dest_neg d) THEN ASM_REWRITE_TAC[]
end g

fun has_cond t = can (find_term (same_const ``COND``)) t

val successful_upd_array_diamond = store_thm(
  "successful_upd_array_diamond",
  ``(a1 ≠ a2 ∨ i1 ≠ i2) ∧ upd_array (m0:memory) a1 i1 v1 = SOME m1 ∧
    upd_array m0 a2 i2 v2 = SOME m2 ⇒
    ∃m. upd_array m2 a1 i1 v1 = SOME m ∧
        upd_array m1 a2 i2 v2 = SOME m``,
  Cases_on `a1 = a2` >| [Cases_on `i1 = i2`, ALL_TAC] >> simp[] >>
  simp[upd_array_def] >> rpt (flookupmem_tac >> simp[]) >>
  map_every (fn q => Cases_on q >> simp[]) [`i1 < 0`, `i2 < 0`] >>
  rpt disjneq_search >> rw[] >> fs[FLOOKUP_UPDATE] >> rw[] >>
  rpt (first_x_assum (mp_tac o assert (has_cond o concl)) >> simp[]) >>
  rw[] >> rw[] >| [
    `0 ≤ i1 ∧ 0 ≤ i2` by ARITH_TAC >>
    `i1 = &(Num i1) ∧ i2 = &(Num i2)` by metis_tac[integerTheory.INT_OF_NUM] >>
    rpt AP_TERM_TAC >>
    qmatch_assum_rename_tac `¬(&LENGTH vl ≤ i1)` [] >>
    `Num i1 < LENGTH vl ∧ Num i2 < LENGTH vl`
              by (fs[integerTheory.INT_NOT_LE] >>
                  metis_tac[integerTheory.INT_LT]) >>
    simp[LIST_EQ_REWRITE, LUPDATE_SEM] >> rw[] >>
    `Num i1 ≠ Num i2`
      by metis_tac[integerTheory.INT_INJ, integerTheory.INT_OF_NUM],
    simp[FUPDATE_COMMUTES]
  ])

val FLOOKUP_EQ_NONE = store_thm(
  "FLOOKUP_EQ_NONE[simp]",
  ``FLOOKUP f k = NONE ⇔ k ∉ FDOM f``,
  simp[FLOOKUP_DEF]);

val successful_updf_diamond = store_thm(
  "successful_updf_diamond",
  ``w1 ≠ w2 ∧ updf w1 v1 m0 = SOME m1 ∧ updf w2 v2 m0 = SOME m2 ⇒
    ∃m. updf w1 v1 m2 = SOME m ∧ updf w2 v2 m1 = SOME m``,
  simp[updf_def] >> Cases_on `w1` >> Cases_on `w2` >> simp[]
  >- metis_tac[successful_upd_array_diamond] >>
  simp[upd_array_def, upd_var_def] >>
  rpt (flookupmem_tac >> simp[]) >> rw[] >>
  rpt disjneq_search >> rw[] >> fs[FLOOKUP_UPDATE] >>
  rpt (first_x_assum (mp_tac o assert (has_cond o concl)) >> simp[]) >>
  rw[] >> fs[FLOOKUP_DEF, FUPDATE_COMMUTES, FAPPLY_FUPDATE_THM] >>
  first_x_assum (mp_tac o assert (has_cond o concl)) >> simp[]);

val updf_writes_commute = store_thm(
  "updf_writes_commute",
  ``w1 ≠ w2 ∧
    updf w1 v1 m0 = SOME m11 ∧ updf w2 v2 m11 = SOME m12 ∧
    updf w2 v2 m0 = SOME m21 ∧ updf w1 v1 m21 = SOME m22 ⇒
    m12 = m22``,
  metis_tac[successful_updf_diamond, optionTheory.SOME_11]);

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
    metis_tac[nontouching_updfs_expreval, touches_SYM],
    ALL_TAC
  ]
end g

val success_case =
  rpt (first_x_assum (kall_tac o assert (is_forall o concl))) >>
  map_every qunabbrev_tac [`A1U`, `A2U`] >> fs[] >>
  qabbrev_tac `
    ae = λa:(value list -> value,actionRW,α)action m.
             a.data (MAP (lookupRW m) a.reads)
  ` >> fs[] >>
  ae_equate_tac "a1" >> ae_equate_tac "a2" >> fs[] >>
  metis_tac[updf_writes_commute]


val apply_action_commutes = store_thm(
  "apply_action_commutes",
  ``a1:(value list -> value,actionRW,α)action ≁ₜ
    a2:(value list -> value,actionRW,α)action ⇒
    apply_action a2 (apply_action a1 m) = apply_action a1 (apply_action a2 m)``,
  strip_tac >>
  `m = NONE ∨ ∃gm. m = SOME gm`
     by metis_tac[optionTheory.option_CASES, pair_CASES] >>
  simp[apply_action_def, lift_OPTION_BIND, combinTheory.o_ABS_R,
       o_UNCURRY_R, C_UNCURRY_L,
       combinTheory.C_ABS_L] >>
  `a1.writes = [] ∨ ∃w1 t1. a1.writes = w1::t1`
    by (Cases_on `a1.writes` >> simp[]) >>
  `a2.writes = [] ∨ ∃w2 t2. a2.writes = w2::t2`
    by (Cases_on `a2.writes` >> simp[]) >>
  simp[] >>
  qabbrev_tac `
    A1U = λm. updf w1 (a1.data (MAP (lookupRW m) a1.reads)) m` >>
  qabbrev_tac `
    A2U = λm. updf w2 (a2.data (MAP (lookupRW m) a2.reads)) m` >>
  simp[] >>
  `(∀m m'. A1U m = SOME m' ⇒ FDOM m' = FDOM m) ∧
   (∀m m'. A2U m = SOME m' ⇒ FDOM m' = FDOM m)`
     by (simp[Abbr`A1U`, Abbr`A2U`] >> metis_tac[updf_preserves_FDOMs]) >>
  `(∀rd. MEM rd a1.reads ⇒ rd ≠ w2) ∧ (∀rd. MEM rd a2.reads ⇒ rd ≠ w1) ∧
   w1 ≠ w2`
    by metis_tac[touches_def, MEM] >>
  rpt (findOptionCases >> simp[]) >> fs[] >>
  TRY (eqNONE_tac >> NO_TAC) >>
  success_case)

val expr_reads_def = tDefine "expr_reads" `
  (expr_reads m (VRead vnm) = [Variable vnm]) ∧
  (expr_reads m (ARead a i_e) =
     (case evalexpr m i_e of
          Int i => CONS (Array a i)
       | _ => I)
     (expr_reads m i_e)) ∧
  (expr_reads m (Opn f elist) = FLAT (MAP (expr_reads m) elist)) ∧
  (expr_reads m (Value v) = [])
` (WF_REL_TAC `measure (λ(m,e). expr_size e)` >> simp[] >>
   Induct >> simp[expr_size_def] >> rpt strip_tac >> simp[] >>
   res_tac >> simp[])

val readAction_def = Define`
  readAction i m e = <| reads := expr_reads m e;
                      writes := [];
                      data := ARB : value list -> value;
                      ident := i |>
`;

val readAction_ident = store_thm(
  "readAction_ident[simp]",
  ``(readAction i m e).ident = i``,
  simp[readAction_def]);

val domreadAction_def = Define`
  domreadAction i m (D lo hi) =
    <| reads := expr_reads m lo ++ expr_reads m hi;
       writes := [];
       data := ARB : value list -> value;
       ident := i |>
`;

val domreadAction_ident = store_thm(
  "domreadAction_ident[simp]",
  ``(domreadAction i m d).ident = i``,
  Cases_on `d` >> simp[domreadAction_def]);

val dvread_def = Define`
  dvread m (DValue _) = [] ∧
  dvread m (DARead _ e) = expr_reads m e ∧
  dvread m (DVRead _) = []
`;

val dvreadAction_def = Define`
  dvreadAction i m ds = <| reads := FLAT (MAP (dvread m) ds);
                           writes := [];
                           data := ARB : value list -> value;
                           ident := i |>
`

val dvreadAction_ident = store_thm(
  "dvreadAction_ident[simp]",
  ``(dvreadAction i m ds).ident = i``,
  simp[dvreadAction_def]);

val apply_dvreadAction = store_thm(
  "apply_dvreadAction[simp]",
  ``apply_action (dvreadAction i m1 ds) m2 = m2``,
  simp[apply_action_def, dvreadAction_def]);

val expr_ind' = store_thm(
  "expr_ind'",
  ``∀P. (∀v. P (Value v)) ∧
        (∀f l. (∀e. MEM e l ⇒ P e) ⇒ P (Opn f l)) ∧
        (∀anm e. P e ⇒ P (ARead anm e)) ∧
        (∀s. P (VRead s)) ⇒
        ∀e. P e``,
  gen_tac >> strip_tac >>
  `(!e. P e) ∧ (∀l e. MEM e l ⇒ P e)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:expr``) >> simp[] >>
  metis_tac[]);

val apply_action_expr_eval_commutes = store_thm(
  "apply_action_expr_eval_commutes",
  ``∀a e j m0 m.
       readAction j m0 e ≁ₜ a ∧ apply_action a (SOME m0) = SOME m ⇒
       evalexpr m e = evalexpr m0 e ∧ readAction j m e = readAction j m0 e``,
  simp[readAction_def, touches_def, apply_action_def] >> gen_tac >>
  `a.writes = [] ∨ ∃w t. a.writes = w::t` by (Cases_on `a.writes` >> simp[]) >>
  simp[] >>
  REWRITE_TAC [DECIDE ``p \/ q <=> ~p ==> q``] >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  pop_assum kall_tac >> map_every qx_gen_tac [`e`, `m0`, `m`] >> strip_tac >>
  first_x_assum (kall_tac o assert (is_forall o concl)) >> rpt (pop_assum mp_tac) >>
  map_every qspec_tac [(`a.data`, `expr`), (`a.reads`, `rds`)] >>
  map_every qid_spec_tac [`m0`, `m`, `e`] >> ho_match_mp_tac expr_ind' >>
  simp[evalexpr_def, expr_reads_def] >> rpt conj_tac
  >- (simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
      AP_TERM_TAC >> simp[MAP_EQ_f] >> metis_tac[])
  >- (map_every qx_gen_tac [`anm`, `e`] >> strip_tac >>
      map_every qx_gen_tac [`m`, `m0`, `rds`, `expr`] >>
      rpt strip_tac >>
      `¬MEM w (expr_reads m0 e)` by (Cases_on `evalexpr m0 e` >> fs[]) >>
      `evalexpr m e = evalexpr m0 e ∧ expr_reads m e = expr_reads m0 e`
        by metis_tac[] >>
      simp[] >> Cases_on `evalexpr m0 e` >> simp[] >> fs[] >>
      qpat_assum `updf xx yy zz = SOME mm` mp_tac >>
      simp[updf_def] >> Cases_on `w` >> simp[]
      >- (simp[upd_array_def] >> flookupmem_tac >> simp[] >>
          rw[lookup_array_def] >> rw[FLOOKUP_UPDATE] >> simp[] >>
          rw[] >> simp[EL_LUPDATE] >> fs[] >>
          qmatch_assum_rename_tac `¬MEM (Array anm j) (expr_reads m0 e)` [] >>
          `0 ≤ i ∧ 0 ≤ j` by ARITH_TAC >>
          `i = &(Num i) ∧ j = &(Num j)`
            by metis_tac[integerTheory.INT_OF_NUM] >>
          qmatch_assum_rename_tac `¬(&LENGTH vl ≤ i)` [] >>
          `Num j < LENGTH vl`
              by (fs[integerTheory.INT_NOT_LE] >>
                  metis_tac[integerTheory.INT_LT]) >>
          metis_tac[]) >>
      simp[upd_var_def] >> rw[] >> simp[lookup_array_def, FLOOKUP_UPDATE] >>
      Cases_on `anm = s` >> simp[] >> flookupmem_tac >> simp[] >>
      fs[FLOOKUP_DEF] >>
      Cases_on `expr (MAP (lookupRW m0) rds)` >> simp[] >> fs[])
  >- (rpt gen_tac >> simp[updf_def] >> Cases_on `w` >>
      simp[upd_array_def, upd_var_def]
      >- (flookupmem_tac >> simp[] >> rw[lookup_v_def] >> Cases_on `s = s'` >>
          simp[FLOOKUP_UPDATE]) >>
      rw[lookup_v_def] >> simp[FLOOKUP_UPDATE]))

val _ = export_theory();
