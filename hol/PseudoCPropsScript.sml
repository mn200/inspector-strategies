open HolKernel Parse boolLib bossLib;

open lcsymtacs

open bagTheory
open PseudoCTheory
open actionGraphTheory
open pred_setTheory finite_mapTheory
open intLib
open pairTheory listTheory rich_listTheory
open boolSimps

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
    SUM (MAP stmt_weight stmts) + 1 + LENGTH stmts) ∧
  (stmt_weight (Par stmts) =
    SUM (MAP stmt_weight stmts) + 1 + LENGTH stmts)
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
     FOLDR (λms b. BAG_UNION (loopbag ms) b) {|0|} stmts) ∧
  (loopbag (Par stmts) =
     FOLDR (λms b. BAG_UNION (loopbag ms) b) {|0|} stmts)
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
              (REWRITE_RULE [GSYM AND_IMP_INTRO] FOLDR_CONG))]);

val _ = overload_on (
  "evalR",
  ``inv_image (mlt (<) LEX (<)) (λ(m:memory,s). (loopbag s, stmt_weight s))``
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


val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ evalR b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[LEX_DEF, MAX_SET_THM, SUM_APPEND]
  >- (Cases_on `b` >> simp[])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- simp[FOLDR_MAP, mlt_loopbag_lemma]
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- simp[FOLDR_MAP, mlt_loopbag_lemma]
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
      Induct_on `sfx` >> simp[])
  >- (disj2_tac >> simp[SUM_APPEND] >> rw[] >>
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

val pushG_def = Define`pushG v = imap (λi. i ++ [v])`

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

val stackInc_def = Define`stackInc = updLast SUC`
val _ = temp_overload_on ("isuc", ``stackInc``)

val stackInc_11 = store_thm(
  "stackInc_11[simp]",
  ``isuc x = isuc y ⇔ x = y``,
  simp[stackInc_def] >>
  rw[updLast_FRONT_LAST] >>
  metis_tac[APPEND_FRONT_LAST]);

val updf_def = Define`
  updf w value m =
    case w of
      | Array a i => upd_array m a i value
      | Variable vnm => upd_var m vnm value
`;

val apply_action_def = Define`
  apply_action a m_opt =
    case a.write of
        NONE => m_opt
      | SOME w =>
        do
          m <- m_opt;
          vs <- SOME(MAP (lookupRW m) a.reads);
          value <- SOME (a.expr vs);
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
  simp[apply_action_def] >> Cases_on `a.write` >> simp[] >>
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

val nontouching_updfs_read_after_write = store_thm(
  "nontouching_updfs_read_after_write",
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
  ``¬(touches a1 a2) ∧ a2.write = SOME w ∧ updf w value m = SOME m' ⇒
    MAP (lookupRW m') a1.reads = MAP (lookupRW m) a1.reads``,
  simp[MAP_EQ_f] >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  `r ≠ w` by metis_tac[touches_def] >>
  metis_tac[nontouching_updfs_read_after_write]);

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
    metis_tac[nontouching_updfs_read_after_write, touches_def]
  val expr_case =
    rpt disj2_tac >>
    qpat_assum `XX = Array ZZ:value`
      (fn th => EXISTS_TAC (rand (rhs (concl th))) THEN
                REWRITE_TAC [SYM th]) >> AP_TERM_TAC >>
    simp[MAP_EQ_f] >> rpt strip_tac >>
    qunabbrev_tac [QUOTE other_name] >> fs[] >>
    metis_tac[nontouching_updfs_read_after_write, touches_def]
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
  `m = NONE ∨ ∃gm. m = SOME gm`
     by metis_tac[optionTheory.option_CASES, pair_CASES] >>
  simp[apply_action_def, lift_OPTION_BIND, combinTheory.o_ABS_R,
       o_UNCURRY_R, C_UNCURRY_L,
       combinTheory.C_ABS_L] >>
  `a1.write = NONE ∨ ∃w1. a1.write = SOME w1`
    by (Cases_on `a1.write` >> simp[]) >>
  `a2.write = NONE ∨ ∃w2. a2.write = SOME w2`
    by (Cases_on `a2.write` >> simp[]) >>
  simp[] >>
  qabbrev_tac `
    A1U = λm. updf w1 (a1.expr (MAP (lookupRW m) a1.reads)) m` >>
  qabbrev_tac `
    A2U = λm. updf w2 (a2.expr (MAP (lookupRW m) a2.reads)) m` >>
  simp[] >>
  `(∀m m'. A1U m = SOME m' ⇒ FDOM m' = FDOM m) ∧
   (∀m m'. A2U m = SOME m' ⇒ FDOM m' = FDOM m)`
     by (simp[Abbr`A1U`, Abbr`A2U`] >> metis_tac[updf_preserves_FDOMs]) >>
  rpt (findOptionCases >> simp[]) >> fs[] >>
  TRY (eqNONE_tac >> NO_TAC) >>
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

val pcg_eval_imap_irrelevance = store_thm(
  "pcg_eval_imap_irrelevance[simp]",
  ``pcg_eval (imap f g) m = pcg_eval g m``,
  simp[pcg_eval_def] >> match_mp_tac gEVAL_imap_irrelevance >>
  simp[commutes_lemma] >> simp[apply_action_def]);

val MAPi_def = Define`
  (MAPi f [] = []) ∧
  (MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t)
`;
val _ = export_rewrites ["MAPi_def"]

val LT_SUC = prove(
  ``n < SUC m ⇔ n = 0 ∨ ∃n0. n = SUC n0 ∧ n0 < m``,
  simp[EQ_IMP_THM] >> Cases_on `n` >> simp[]);

val MEM_MAPi = store_thm(
  "MEM_MAPi",
  ``∀x f l. MEM x (MAPi f l) ⇔
            ∃n. n < LENGTH l ∧ x = f n (EL n l)``,
  Induct_on `l` >> simp[] >> pop_assum kall_tac >>
  dsimp[EQ_IMP_THM, LT_SUC] >> metis_tac[]);

val MAPi_CONG = store_thm(
  "MAPi_CONG",
  ``∀l1 l2 f1 f2.
      l1 = l2 ∧ (∀x n. MEM x l2 ∧ n < LENGTH l2 ⇒ f1 n x = f2 n x) ⇒
      MAPi f1 l1 = MAPi f2 l2``,
  Induct_on `l1` >> dsimp[LT_SUC]);
val _ = DefnBase.export_cong "MAPi_CONG"

val MAPi_CONG' = store_thm(
  "MAPi_CONG'",
  ``l1 = l2 ⇒ (∀x n. (x = EL n l2) ⇒ n < LENGTH l2 ⇒ f1 n x = f2 n x) ⇒
    MAPi f1 l1 = MAPi f2 l2``,
  map_every qid_spec_tac [`f1`, `f2`, `l2`] >> Induct_on `l1` >>
  dsimp[LT_SUC]);

val LENGTH_MAPi = store_thm(
  "LENGTH_MAPi[simp]",
  ``∀f l. LENGTH (MAPi f l) = LENGTH l``,
  Induct_on `l` >> simp[]);

val MAP_MAPi = store_thm(
  "MAP_MAPi[simp]",
  ``∀f g l. MAP f (MAPi g l) = MAPi ((o) f o g) l``,
  Induct_on `l` >> simp[]);

val EL_MAPi = store_thm(
  "EL_MAPi[simp]",
  ``∀f n l. n < LENGTH l ⇒ EL n (MAPi f l) = f n (EL n l)``,
  Induct_on `l` >> simp[] >> dsimp[LT_SUC]);

val FOLDRi_def = Define`
  (FOLDRi f a [] = a) ∧
  (FOLDRi f a (h::t) = f 0 h (FOLDRi (f o SUC) a t))`
val _ = export_rewrites ["FOLDRi_def"]

val FOLDR_MAPi = store_thm(
  "FOLDR_MAPi",
  ``∀f g a l. FOLDR f a (MAPi g l) = FOLDRi ($o f o g) a l``,
  Induct_on `l` >> simp[MAPi_def]);

val expr_reads_def = tDefine "expr_reads" `
  (expr_reads m (VarExp vnm) = [Variable vnm]) ∧
  (expr_reads m (ISub a i_e) =
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
                      write := NONE;
                      expr := ARB : value list -> value;
                      iter := i |>
`;

val readAction_iter = store_thm(
  "readAction_iter[simp]",
  ``(readAction i m e).iter = i``,
  simp[readAction_def]);

val domreadAction_def = Define`
  domreadAction i m (D lo hi) =
    <| reads := expr_reads m lo ++ expr_reads m hi;
       write := NONE;
       expr := ARB : value list -> value;
       iter := i |>
`;

val domreadAction_iter = store_thm(
  "domreadAction_iter[simp]",
  ``(domreadAction i m d).iter = i``,
  Cases_on `d` >> simp[domreadAction_def]);

val dvread_def = Define`
  dvread m (DValue _) = [] ∧
  dvread m (ARead _ e) = expr_reads m e ∧
  dvread m (VRead _) = []
`;

val dvreadAction_def = Define`
  dvreadAction i m ds = <| reads := FLAT (MAP (dvread m) ds);
                           write := NONE;
                           expr := ARB : value list -> value;
                           iter := i |>
`

val dvreadAction_iter = store_thm(
  "dvreadAction_iter[simp]",
  ``(dvreadAction i m ds).iter = i``,
  simp[dvreadAction_def]);

val apply_dvreadAction = store_thm(
  "apply_dvreadAction[simp]",
  ``apply_action (dvreadAction i m1 ds) m2 = m2``,
  simp[apply_action_def, dvreadAction_def]);

val graphOf_def = tDefine "graphOf" `

  (graphOf i0 m0 (IfStmt gd t e) =
     case evalexpr m0 gd of
       | Bool T => do
                     (i,m,g) <- graphOf (stackInc i0) m0 t;
                     SOME(i,m,readAction i0 m0 gd ⊕ g)
                   od
       | Bool F => do
                     (i,m,g) <- graphOf (stackInc i0) m0 e;
                     SOME(i,m,readAction i0 m0 gd ⊕ g)
                   od
       | _ => NONE) ∧

  (graphOf i0 m0 (ForLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       (i,m,g) <- graphOf (stackInc i0) m0
                          (Seq (MAP (λv. ssubst vnm v body) dvs));
       SOME(i,m,domreadAction i0 m0 d ⊕ g)
     od) ∧

  (graphOf i0 m0 (Seq cmds) =
     case cmds of
       | [] => SOME (i0, m0, emptyG)
       | c :: rest =>
         do
           (i1, m1, G1) <- graphOf i0 m0 c;
           (i2, m2, G2) <- graphOf i1 m1 (Seq rest);
           SOME(i2,m2,merge_graph G1 G2)
         od) ∧

  (graphOf i0 m0 (ParLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       (i,m,g) <- graphOf (stackInc i0) m0
                          (Par (MAP (λv. ssubst vnm v body) dvs));
       SOME(i,m,domreadAction i0 m0 d ⊕ g)
     od) ∧

  (graphOf i0 m0 (Par cmds) =
     do
       ps <-
         OPT_SEQUENCE
           (MAPi (λn c. OPTION_MAP (SND o SND) (graphOf (i0 ++ [n;0]) m0 c)) cmds);
       assert(∀i j. i < j ∧ j < LENGTH ps ⇒ ¬gtouches (EL i ps) (EL j ps));
       g <- SOME (FOLDR merge_graph emptyG ps);
       m <- pcg_eval g (SOME m0);
       SOME(stackInc i0, m, g)
     od) ∧

  (graphOf i0 m0 (Assign w ds opn) =
     do (aname,i_e) <- SOME w;
        i <- (some i. evalexpr m0 i_e = Int i);
        rds <- getReads m0 ds;
        a0 <- SOME (readAction i0 m0 i_e);
        a1 <- SOME (dvreadAction (stackInc i0) m0 ds);
        a <- SOME <| write := SOME(Array aname i);
                     reads := rds;
                     expr := mergeReads ds opn;
                     iter := stackInc (stackInc i0) |> ;
        rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
        m' <- upd_array m0 aname i (opn rvs);
        SOME(stackInc (stackInc (stackInc i0)), m', a0 ⊕ (a1 ⊕ (a ⊕ emptyG)))
     od) ∧

  (graphOf i0 m0 (AssignVar vnm e) =
     do
       m' <- updf (Variable vnm) (evalexpr m0 e) m0;
       SOME(stackInc i0, m',
            <| write := SOME (Variable vnm);
               reads := expr_reads m0 e;
               expr := K (evalexpr m0 e);
               iter := i0 |> ⊕ emptyG)
     od) ∧

  (graphOf i0 m0 Abort = NONE) ∧

  (graphOf i0 m0 Done = SOME(i0,m0,emptyG)) ∧

  (graphOf i0 m0 (Malloc vnm sz value) = NONE)

` (WF_REL_TAC
     `inv_image (mlt (<) LEX (<)) (λ(i,m,s). (loopbag s, stmt_weight s))` >>
   simp[WF_mlt1, FOLDR_MAP, mlt_loopbag_lemma] >>
   rpt strip_tac
   >- (imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `I` mp_tac) >>
       rw[] >> simp[] >> qpat_assum `MEM c cmds` mp_tac >>
       rpt (pop_assum kall_tac) >>
       qid_spec_tac `c` >> Induct_on `cmds` >> dsimp[] >>
       rpt strip_tac >> res_tac >> decide_tac))

val eval_ind' =
    eval_strongind |> SIMP_RULE (srw_ss()) [FORALL_PROD]
                   |> Q.SPEC `\a1 a2. P (FST a1) (SND a1) (FST a2) (SND a2)`
                   |> SIMP_RULE (srw_ss()) []

val _ = overload_on ("<", ``\il1:num list il2. LLEX $< il1 il2``)
val _ = overload_on ("<=", ``\il1:num list il2. ¬LLEX $< il2 il1``)

val ilist_trichotomy = store_thm(
  "ilist_trichotomy",
  ``∀x y:num list. x < y ∨ x = y ∨ y < x``,
  metis_tac[LLEX_total
              |> GEN_ALL |> Q.ISPEC `$< : num -> num -> bool`
              |> SIMP_RULE (srw_ss() ++ ARITH_ss)
                   [relationTheory.total_def, relationTheory.RC_DEF]])

val ilistLT_trans = save_thm(
  "ilistLT_trans",
  LLEX_transitive
    |> GEN_ALL |> Q.ISPEC `$< : num -> num -> bool`
    |> SIMP_RULE (srw_ss() ++ ARITH_ss) [relationTheory.transitive_def]);

val ilistLE_REFL = store_thm(
  "ilistLE_REFL[simp]",
  ``∀x:num list. x ≤ x``,
  Induct >> simp[]);

val ilistLE_LTEQ = store_thm(
  "ilistLE_LTEQ",
  ``(x:num list) ≤ y ⇔ x < y ∨ x = y``,
  metis_tac[ilist_trichotomy, ilistLT_trans, ilistLE_REFL]);

val ilistLE_trans = store_thm(
  "ilistLE_trans",
  ``(x:num list) ≤ y ∧ y ≤ z ⇒ x ≤ z``,
  metis_tac[ilistLE_LTEQ, ilistLT_trans]);

val ilistLET_trans = store_thm(
  "ilistLET_trans",
  ``(x:num list) ≤ y ∧ y < z ⇒ x < z``,
  metis_tac[ilistLE_LTEQ, ilistLT_trans]);

val ilistLTE_trans = store_thm(
  "ilistLTE_trans",
  ``(x:num list) < y ∧ y ≤ z ⇒ x < z``,
  metis_tac[ilistLE_LTEQ, ilistLT_trans]);

val ilistLE_antisym = store_thm(
  "ilistLE_antisym",
  ``(x:num list) ≤ y ∧ y ≤ x ⇒ x = y``,
  metis_tac[ilist_trichotomy]);

val OPTION_IGNORE_BIND_EQUALS_OPTION = store_thm(
  "OPTION_IGNORE_BIND_EQUALS_OPTION[simp]",
  ``((OPTION_IGNORE_BIND x y = NONE) <=> (x = NONE) \/ (y = NONE)) /\
    ((OPTION_IGNORE_BIND x y = SOME z) <=>
      (?x'. x = SOME x') /\ (y = SOME z))``,
  Cases_on `x` THEN SIMP_TAC (srw_ss()) []);

val iterations_FOLDR_merge_graph = store_thm(
  "iterations_FOLDR_merge_graph",
  ``i ∈ iterations (FOLDR merge_graph g0 glist) ⇔
    i ∈ iterations g0 ∨ ∃g. MEM g glist ∧ i ∈ iterations g``,
  Induct_on `glist` >> simp[] >> metis_tac[]);

val SNOC_11 = prove(
  ``INJ (λi. i ++ [x]) s UNIV``,
  simp[INJ_THM]);

val iterations_pushG = store_thm(
  "iterations_pushG",
  ``i ∈ iterations (pushG n g) ⇔
    ∃i0. i0 ∈ iterations g ∧ i = i0 ++ [n]``,
  simp[pushG_def, SNOC_11, iterations_imap] >> metis_tac[]);

val ilistLE_NIL = store_thm(
  "ilistLE_NIL[simp]",
  ``(x:num list) ≤ [] ⇔ (x = [])``,
  simp[ilistLE_LTEQ]);

val ilistLT_stackInc = store_thm(
  "ilistLT_stackInc[simp]",
  ``i ≠ [] ⇒ i < stackInc i ∧ i ≤ stackInc i``,
  csimp[ilistLE_LTEQ] >> simp[stackInc_def] >>
  Induct_on `i` >> simp[] >>
  Cases_on `i` >> simp[]);

val LENGTH_updLast = store_thm(
  "LENGTH_updLast[simp]",
  ``LENGTH (updLast f l) = LENGTH l``,
  Induct_on `l` >> simp[] >> Cases_on `l` >> simp[]);

val LENGTH_stackInc = store_thm(
  "LENGTH_stackInc[simp]",
  ``LENGTH (stackInc l) = LENGTH l``,
  simp[stackInc_def]);

val stackInc_id = store_thm(
  "stackInc_id[simp]",
  ``(stackInc it = it ⇔ it = []) ∧ (it = stackInc it ⇔ it = []) ∧
    (isuc (isuc it) = it ⇔ it = []) ∧ (it = isuc (isuc it) ⇔ it = [])``,
  simp[stackInc_def, updLast_FRONT_LAST] >> Cases_on `it = []` >>
  simp[FRONT_APPEND] >>
  imp_res_tac APPEND_FRONT_LAST >>
  metis_tac[APPEND_11, CONS_11, DECIDE ``SUC x ≠ x ∧ SUC (SUC x) ≠ x``]);

val updLast_EQ_NIL = store_thm(
  "updLast_EQ_NIL[simp]",
  ``updLast f l = [] ⇔ l = []``,
  Induct_on `l` >> simp[] >> Cases_on `l` >> simp[]);

val stackInc_EQ_NIL = store_thm(
  "stackInc_EQ_NIL[simp]",
  ``stackInc l = [] ⇔ l = []``,
  simp[stackInc_def]);

val FRONT_updLast = store_thm(
  "FRONT_updLast[simp]",
  ``l ≠ [] ⇒ FRONT (updLast f l) = FRONT l``,
  Induct_on `l` >> simp[] >>
  Cases_on `l` >> fs[] >>
  Cases_on `updLast f (h::t)` >> simp[] >>
  pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]);

val FRONT_stackInc = store_thm(
  "FRONT_stackInc[simp]",
  ``l ≠ [] ⇒ FRONT (stackInc l) = FRONT l``,
  simp[stackInc_def]);

val OPT_SEQUENCE_EQ_SOME = store_thm(
   "OPT_SEQUENCE_EQ_SOME",
   ``∀l. OPT_SEQUENCE optlist = SOME l ⇔
         (∀e. MEM e optlist ⇒ ∃v. e = SOME v) ∧
         (l = MAP THE optlist)``,
   Induct_on `optlist` >> dsimp[OPT_SEQUENCE_def] >>
   csimp[] >> metis_tac []);

val ilistLE_APPEND = store_thm(
  "ilistLE_APPEND[simp]",
  ``(x:num list) ≤ x ++ y``,
  Induct_on `x` >> simp[]);

val FRONT_TAKE = store_thm(
  "FRONT_TAKE",
  ``l ≠ [] ⇒ FRONT l = TAKE (LENGTH l - 1) l``,
  Induct_on `l` >> simp[] >> Cases_on `l` >>
  fs[DECIDE ``SUC x ≤ 1 ⇔ x = 0``]);

val TAKE_isPREFIX = store_thm(
  "TAKE_isPREFIX",
  ``!n l. n <= LENGTH l ==> TAKE n l <<= l``,
  Induct_on `l` THEN SIMP_TAC (srw_ss()) [] THEN
  MAP_EVERY Q.X_GEN_TAC [`h`, `n`] THEN STRIP_TAC THEN
  `n < SUC (LENGTH l) \/ n = SUC (LENGTH l)` by DECIDE_TAC THENL [
    FULL_SIMP_TAC (srw_ss()) [LT_SUC] THEN SRW_TAC[][] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val stackInc_TAKE_lemma = prove(
  ``∀l1 l2. l1 ≼ l2 ∧ l1 ≠ [] ⇒ l2 < stackInc l1``,
  simp[stackInc_def] >> Induct_on `l1` >> simp[] >> Cases_on `l2` >>
  simp[] >> Cases_on `l1` >> simp[]);

val graphOf_iterations_apart = store_thm(
  "graphOf_iterations_apart",
  ``∀i0 m0 c i m g.
       graphOf i0 m0 c = SOME(i,m,g) ∧ i0 ≠ [] ⇒
       i0 ≤ i ∧ LENGTH i = LENGTH i0 ∧ FRONT i = FRONT i0 ∧
       ∀j. j ∈ iterations g ⇒ i0 ≤ j ∧ j < i ∧
           LENGTH i0 ≤ LENGTH j ∧
           TAKE (LENGTH i0 - 1) j = FRONT i0``,
  ho_match_mp_tac (theorem "graphOf_ind") >> rpt conj_tac

  >- ((* if *)
      ONCE_REWRITE_TAC [graphOf_def] >>
      map_every qx_gen_tac [`i0`, `m0`, `gd`, `ts`, `es`] >>
      Cases_on `evalexpr m0 gd` >> simp[] >>
      qmatch_assum_rename_tac `evalexpr m0 gd = Bool b` [] >>
      Cases_on `b` >>
      simp[EXISTS_PROD, PULL_EXISTS] >>
      strip_tac >> rpt gen_tac >> strip_tac >> fs[] >>
      `i0 < stackInc i0` by metis_tac[ilistLT_stackInc] >>
      `i0 < i` by metis_tac[ilistLTE_trans] >>
      `i0 ≤ i` by simp[ilistLE_LTEQ] >>
      dsimp[] >>
      metis_tac[FRONT_TAKE, ilistLTE_trans, ilistLE_LTEQ])
  >- ((* forloop *)
      map_every qx_gen_tac [`i0`, `m0`, `vnm`, `d`, `body`] >>
      strip_tac >> simp[Once graphOf_def] >>
      simp[EXISTS_PROD, PULL_EXISTS] >>
      map_every qx_gen_tac [`i`, `m`, `dvs`, `g`] >> strip_tac >>
      fs[] >> dsimp[FRONT_TAKE] >>
      `i0 < stackInc i0` by metis_tac[ilistLT_stackInc] >>
      metis_tac[ilistLTE_trans, ilistLE_LTEQ])
  >- ((* Seq *)
      map_every qx_gen_tac [`i0`, `m0`, `cmds`] >> strip_tac >>
      simp[Once graphOf_def] >> Cases_on `cmds` >> simp[] >>
      map_every qx_gen_tac [`i`, `m`, `g`] >>
      simp[PULL_EXISTS, FORALL_PROD] >>
      map_every qx_gen_tac [`i'`, `m'`, `g'`, `g''`] >> strip_tac >>
      `i0 ≤ i' ∧ i' ≤ i ∧ i' ≠ [] ∧ LENGTH i' = LENGTH i0 ∧
       LENGTH i = LENGTH i0 ∧ FRONT i' = FRONT i0 ∧ FRONT i = FRONT i0`
        by metis_tac[ilistLE_NIL] >>
      `i0 ≤ i` by metis_tac[ilistLE_trans] >> simp[] >>
      qx_gen_tac `j` >> rw[] >>
      metis_tac[ilistLTE_trans, ilistLE_trans])
  >- ((* ParLoop *)
      rpt gen_tac >> strip_tac >>
      simp[Once graphOf_def, PULL_EXISTS, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m`, `dvs`, `g`] >> strip_tac >> fs[] >>
      dsimp[FRONT_TAKE] >>
      `i0 < stackInc i0` by metis_tac[ilistLT_stackInc] >>
      metis_tac[ilistLTE_trans, ilistLE_LTEQ])
  >- ((* Par *)
      map_every qx_gen_tac [`i0`, `m0`, `c`] >> strip_tac >>
      simp[Once graphOf_def, PULL_EXISTS, iterations_FOLDR_merge_graph,
           PULL_EXISTS, iterations_pushG, ilistLT_stackInc,
           OPT_SEQUENCE_EQ_SOME, MEM_MAPi, MEM_MAP,
           EXISTS_PROD, combinTheory.o_ABS_R] >>
      qabbrev_tac `GG = λn. graphOf (i0 ++ [n;0]) m0 (EL n c)` >> simp[] >>
      qx_gen_tac `m` >> strip_tac >>
      map_every qx_gen_tac [`j`, `n`] >> strip_tac >>
      `∃i' m' g'. GG n = SOME(i',m',g')` by metis_tac[] >> fs[] >>
      first_x_assum (qspecl_then [`EL n c`, `n`] mp_tac) >>
      simp[EL_MEM] >> strip_tac >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
      `i0 ≤ i0 ++ [n; 0]` by simp[] >>
      `i0 ≤ j` by metis_tac[ilistLE_trans] >>
      fs[FRONT_APPEND] >>
      `0 < LENGTH i0`
        by (spose_not_then assume_tac >> fs[LENGTH_NIL]) >>
      `TAKE (LENGTH i0 - 1) j = FRONT i0`
        by (qpat_assum `TAKE xx j = yy`
              (mp_tac o Q.AP_TERM `TAKE (LENGTH i0 - 1)`) >>
            simp[TAKE_TAKE, TAKE_APPEND1,
                 FRONT_TAKE]) >> simp[] >>
      `j < stackInc i0`
        by (match_mp_tac stackInc_TAKE_lemma >> simp[] >>
            qpat_assum `TAKE xx j = i0 ++ [n]`
              (mp_tac o Q.AP_TERM `TAKE (LENGTH i0)`) >>
            simp[TAKE_APPEND1, TAKE_TAKE] >>
            qabbrev_tac `N = LENGTH i0` >>
            disch_then (SUBST1_TAC o SYM) >>
            `N ≤ LENGTH j` by simp[] >> simp[TAKE_isPREFIX]))
  >- ((* Assign *)
      simp[Once graphOf_def, FORALL_PROD, PULL_EXISTS] >>
      map_every qx_gen_tac [`i0`, `m0`, `w`, `i_e`, `ds`, `opn`, `m`] >>
      rpt gen_tac >> strip_tac >> dsimp[] >>
      `i0 < stackInc i0 ∧ stackInc i0 < stackInc (stackInc i0) ∧
       stackInc (stackInc i0) < stackInc (stackInc (stackInc i0))`
        by metis_tac[ilistLT_stackInc, stackInc_EQ_NIL] >>
      metis_tac[FRONT_TAKE, LENGTH_stackInc, FRONT_stackInc,
                stackInc_EQ_NIL, ilistLT_trans, ilistLE_LTEQ])
  >- ((* AssignVar *)
      simp[Once graphOf_def, FRONT_TAKE])
  >- ((* Abort *) simp[Once graphOf_def])
  >- ((* Done *) simp[Once graphOf_def])
  >- ((* Malloc *) simp[graphOf_def])
);

val pcg_eval_merge_graph = store_thm(
  "pcg_eval_merge_graph",
  ``(∀a. a ∈ g1 ⇒ a.iter ∉ iterations g2) ⇒
    pcg_eval (merge_graph g1 g2) m_opt = pcg_eval g2 (pcg_eval g1 m_opt)``,
  map_every qid_spec_tac [`m_opt`, `g2`, `g1`] >>
  ho_match_mp_tac graph_ind >> simp[pcg_eval_thm] >>
  map_every qx_gen_tac [`a`, `g1`] >> strip_tac >>
  dsimp[merge_graph_addaction_ASSOC, pcg_eval_thm]);

val some_EQ_SOME_E = save_thm(
  "some_EQ_SOME_E",
  optionTheory.some_elim
    |> Q.INST [`Q` |-> `\y. y = SOME x`]
    |> SIMP_RULE bool_ss [optionTheory.NOT_SOME_NONE,
                          optionTheory.SOME_11]);

val some_EQ_NONE = store_thm(
  "some_EQ_NONE[simp]",
  ``(some) P = NONE ⇔ ∀x. ¬P x``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC bool_ss [optionTheory.NOT_SOME_NONE] THEN
  METIS_TAC[]);

val assign_lemma = prove(
  ``OPT_SEQUENCE (MAP (evalDexpr m) ds) = SOME rvs ∧
    getReads m ds = SOME rds ⇒
    mergeReads0 ds acc opn (MAP (lookupRW m) rds) =
    (opn:value list -> value) (REVERSE acc ++ rvs)``,
  simp[OPT_SEQUENCE_EQ_SOME,
       MEM_MAP, MAP_MAP_o,
       PULL_EXISTS] >>
  map_every qid_spec_tac [`acc`, `rvs`, `rds`, `ds`] >>
  Induct >> simp[getReads_def, mergeReads0_def] >>
  Cases >> dsimp[getReads_def, mergeReads0_def, evalDexpr_def,
                 lookupRW_def] >>
  simp_tac bool_ss [APPEND,
                    GSYM APPEND_ASSOC] >>
  rpt strip_tac >> imp_res_tac some_EQ_SOME_E >> fs[]);

val add_action_id' = add_action_id |> EQ_IMP_RULE |> #2

val pcg_eval_readAction = store_thm(
  "pcg_eval_readAction[simp]",
  ``pcg_eval (readAction i m e ⊕ g) mo = pcg_eval g mo``,
  Cases_on `i ∈ iterations g` >> simp[pcg_eval_thm, add_action_id'] >>
  simp[readAction_def, apply_action_def]);

val pcg_eval_domreadAction = store_thm(
  "pcg_eval_domreadAction[simp]",
  ``pcg_eval (domreadAction i m d ⊕ g) mo = pcg_eval g mo``,
  Cases_on `i ∈ iterations g` >> simp[pcg_eval_thm, add_action_id'] >>
  Cases_on `d` >> simp[domreadAction_def, apply_action_def]);

val graphOf_pcg_eval = store_thm(
  "graphOf_pcg_eval",
  ``∀i0 m0 c i m g.
      graphOf i0 m0 c = SOME(i,m,g) ∧ i0 ≠ [] ⇒ pcg_eval g (SOME m0) = SOME m``,
  ho_match_mp_tac (theorem "graphOf_ind") >> rpt conj_tac >>
  map_every qx_gen_tac [`i0`, `m0`]
  >- ((* if *)
      map_every qx_gen_tac [`gd`, `t`, `e`] >> strip_tac >>
      simp[graphOf_def] >>
      Cases_on `evalexpr m0 gd` >> simp[] >>
      fs[] >> COND_CASES_TAC >> fs[EXISTS_PROD, PULL_EXISTS])
  >- ((* forloop *)
      rpt gen_tac >> strip_tac >>
      simp[Once graphOf_def, PULL_EXISTS, FORALL_PROD])
  >- ((* seq *)
      qx_gen_tac `cs` >> strip_tac >> simp[Once graphOf_def] >> Cases_on `cs` >>
      simp[pcg_eval_thm, PULL_EXISTS, FORALL_PROD] >>
      fs[] >> map_every qx_gen_tac [`i`, `m`, `i'`, `m'`, `g1`, `g2`] >>
      strip_tac >>
      `i0 ≤ i' ∧ (∀j. j ∈ iterations g1 ⇒ j < i') ∧ i' ≠ [] ∧
       (∀j. j ∈ iterations g2 ⇒ i' ≤ j)`
         by metis_tac[graphOf_iterations_apart, ilistLE_NIL] >>
      `∀a. a ∈ g1 ⇒ a.iter ∉ iterations g2`
        by (fs[iterations_thm, PULL_EXISTS] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      simp[pcg_eval_merge_graph] >> fs[])
  >- ((* parloop *)
      map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      simp[Once graphOf_def, PULL_EXISTS, FORALL_PROD])
  >- ((* par *)
      qx_gen_tac `cs` >> simp[] >> strip_tac >>
      simp[Once graphOf_def, PULL_EXISTS])
  >- ((* assign *)
      simp[graphOf_def, FORALL_PROD, PULL_EXISTS, pcg_eval_thm] >>
      simp[apply_action_def, updf_def] >>
      map_every qx_gen_tac [`vnm`, `i_e`, `ds`, `opn`, `m`, `i`, `rds`, `rvs`] >>
      strip_tac >>
      `mergeReads ds opn (MAP (lookupRW m0) rds) = opn rvs` suffices_by simp[] >>
      imp_res_tac (GEN_ALL assign_lemma) >> simp[mergeReads_def])
  >- ((* assignvar *)
      simp[graphOf_def, pcg_eval_thm, updf_def, apply_action_def])
  >- ((* Abort *) simp[graphOf_def])
  >- ((* Done *) simp[graphOf_def, pcg_eval_thm])
  >- ((* Malloc *) simp[graphOf_def]));

val assert_EQ_SOME = store_thm(
  "assert_EQ_SOME[simp]",
  ``(assert b = SOME x) <=> b``,
  Cases_on `b` THEN SIMP_TAC (srw_ss()) [oneTheory.one]);

val INJ_UNION_DOMAIN = store_thm(
  "INJ_UNION_DOMAIN",
  ``INJ f (p ∪ q) r ⇔
      INJ f p r ∧ INJ f q r ∧
      DISJOINT (IMAGE f (p DIFF q)) (IMAGE f (q DIFF p))``,
  dsimp[INJ_THM, EQ_IMP_THM] >> rw[]
  >- (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]));

val add_postactionID = store_thm(
  "add_postactionID",
  ``a.iter ∈ iterations g ⇒ add_postaction a g = g``,
  simp[graph_equality, add_postaction_edges]);

val imap_add_postaction = store_thm(
  "imap_add_postaction",
  ``INJ f (a.iter INSERT iterations g) UNIV ⇒
    imap f (add_postaction a g) =
        add_postaction (a with iter updated_by f) (imap f g)``,
  map_every qid_spec_tac [`a`, `g`] >> ho_match_mp_tac graph_ind >>
  simp[imap_add_action] >> map_every qx_gen_tac [`a`, `g`] >>
  strip_tac >> qx_gen_tac `b` >> strip_tac >>
  `INJ f (a.iter INSERT iterations g) UNIV` by fs[INJ_INSERT] >>
  `INJ f (b.iter INSERT iterations g) UNIV` by fs[INJ_INSERT] >>
  Cases_on `b.iter = a.iter`
  >- simp[add_postactionID, iterations_imap] >>
  `f a.iter ≠ f b.iter` by fs[INJ_THM] >>
  fs[imap_add_action, add_action_add_postaction_ASSOC, INSERT_COMM]);

val imap_merge_graph = store_thm(
  "imap_merge_graph",
  ``INJ f (iterations g1 ∪ iterations g2) UNIV ∧
    DISJOINT (iterations g1) (iterations g2) ⇒
    imap f (merge_graph g1 g2) = merge_graph (imap f g1) (imap f g2)``,
  map_every qid_spec_tac [`g1`, `g2`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm] >> rpt strip_tac >>
  fs[INSERT_UNION_EQ, ONCE_REWRITE_RULE [UNION_COMM] INSERT_UNION_EQ] >>
  `DISJOINT (iterations g1) (iterations g2) ∧
   DISJOINT (a.iter INSERT iterations g1) (iterations g2)`
    by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `INJ f (a.iter INSERT iterations g1) UNIV ∧
   INJ f (a.iter INSERT iterations g2) UNIV ∧
   INJ f (iterations g1) UNIV ∧ INJ f (iterations g2) UNIV`
    by (fs[INJ_UNION_DOMAIN, INJ_INSERT] >> fs[INJ_THM] >>
        metis_tac[]) >>
  `∀j. j ∈ iterations g1 ∨ j ∈ iterations g2 ⇒ (f a.iter ≠ f j)`
    by (rpt strip_tac >> fs[INJ_INSERT, DISJOINT_DEF, EXTENSION] >>
        metis_tac[]) >>
  csimp[imap_add_action, merge_graph_thm, iterations_imap,
        imap_add_postaction, INSERT_UNION_EQ,
        ONCE_REWRITE_RULE [UNION_COMM] INSERT_UNION_EQ]);

val INJ_CONG = store_thm(
  "INJ_CONG",
  ``(∀x. x ∈ s ⇒ f x = g x) ⇒ (INJ f s t ⇔ INJ g s t)``,
  simp[INJ_THM]);

val iterations_FOLDRi_merge = store_thm(
  "iterations_FOLDRi_merge",
  ``∀g.
      iterations (FOLDRi (λn c. merge_graph (g n c)) a l) =
        BIGUNION (IMAGE (λi. iterations (g i (EL i l))) (count (LENGTH l))) ∪
        iterations a``,
  Induct_on `l` >> simp[combinTheory.o_ABS_L] >>
  dsimp[Once EXTENSION, LT_SUC] >> metis_tac[]);

val match_imp = let
  fun f th = SUBGOAL_THEN (lhand (concl th)) (mp_tac o MATCH_MP th)
in
  disch_then f
end

val imap_FOLDRi_merge = store_thm(
  "imap_FOLDRi_merge",
  ``∀f g.
      (∀i j. i < j ∧ j < LENGTH l ⇒
        DISJOINT (iterations (g i (EL i l)))
                 (iterations (g j (EL j l)))) ∧
      (∀i. i < LENGTH l ⇒
           DISJOINT (iterations (g i (EL i l))) (iterations G)) ∧
      INJ f (iterations G ∪
             iterations (FOLDRi (λn c. merge_graph (g n c)) G l))
            UNIV
     ⇒
      imap f (FOLDRi (λn c. merge_graph (g n c)) G l) =
      FOLDRi (λn c. merge_graph (imap f (g n c))) (imap f G) l``,
  Induct_on `l` >> simp[imap_merge_graph, combinTheory.o_ABS_L, LT_SUC] >>
  dsimp[LT_SUC] >> map_every qx_gen_tac [`h`, `f`, `g`] >>
  strip_tac >>
  first_x_assum (qspecl_then [`f`, `λn c. g (SUC n) c`] mp_tac) >>
  simp[] >>
  imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO] INJ_SUBSET) >>
  fs[] >>
  match_imp >- (first_assum match_mp_tac >> simp[SUBSET_DEF]) >>
  qabbrev_tac `AG = FOLDRi (λn c. merge_graph (g (SUC n) c)) G l` >>
  `imap f (merge_graph (g 0 h) AG) = merge_graph (imap f (g 0 h)) (imap f AG)`
    by (match_mp_tac imap_merge_graph >> conj_tac
        >- (first_x_assum match_mp_tac >> simp[SUBSET_DEF]) >>
        dsimp[Abbr`AG`, iterations_FOLDRi_merge] >>
        metis_tac[DISJOINT_SYM]) >>
  simp[combinTheory.o_DEF]);

val FOLDRi_CONG = store_thm(
  "FOLDRi_CONG",
  ``l1 = l2 ⇒
    (∀n e a. n < LENGTH l2 ⇒ MEM e l2 ⇒ f1 n e a = f2 n e a) ⇒
    a1 = a2 ⇒
    FOLDRi f1 a1 l1 = FOLDRi f2 a2 l2``,
  disch_then SUBST_ALL_TAC >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`f1`, `f2`] >>
  Induct_on `l2` >> simp[] >> dsimp[LT_SUC] >> rpt strip_tac >>
  AP_TERM_TAC >> first_x_assum match_mp_tac >> simp[]);

val FOLDRi_CONG' = store_thm(
  "FOLDRi_CONG'",
  ``l1 = l2 ∧ (∀n a. n < LENGTH l2 ⇒ f1 n (EL n l2) a = f2 n (EL n l2) a) ∧
    a1 = a2 ⇒
    FOLDRi f1 a1 l1 = FOLDRi f2 a2 l2``,
  strip_tac >> rw[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`f1`, `f2`] >> Induct_on `l1` >>
  dsimp[LT_SUC] >> rpt strip_tac >> AP_TERM_TAC >>
  first_x_assum match_mp_tac >> simp[]);

val graphOf_starting_id_irrelevant = store_thm(
  "graphOf_starting_id_irrelevant",
  ``∀i0 m0 c0 i m g.
       graphOf i0 m0 c0 = SOME (i, m, g) ∧ i0 ≠ [] ⇒
       ∀i0'.
        i0' ≠ [] ⇒
        ∃f.
          graphOf i0' m0 c0 = SOME(f i, m, imap f g) ∧
          i0' = f i0 ∧ INJ f (i INSERT iterations g) UNIV``,
  ho_match_mp_tac (theorem "graphOf_ind") >> rpt conj_tac >>
  map_every qx_gen_tac [`i0`, `m0`]
  >- (qx_gen_tac `gd` >> rpt gen_tac >> strip_tac >>
      ONCE_REWRITE_TAC [graphOf_def] >>
      Cases_on `evalexpr m0 gd` >> simp[] >>
      qmatch_assum_rename_tac `evalexpr m0 gd = Bool b` [] >>
      Cases_on `b` >> simp[PULL_EXISTS, EXISTS_PROD] >> fs[] >>
      map_every qx_gen_tac [`i`, `m`, `g`] >> strip_tac >> fs[] >>
      qx_gen_tac `i0'` >> strip_tac >>
      first_x_assum (qspec_then `stackInc i0'` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `f` strip_assume_tac) >> simp[] >>
      qabbrev_tac `ff = λj. if j = i0 then i0' else f j` >>
      qexists_tac `ff` >> simp[] >>
      `stackInc i0 ≤ i ∧ ∀j. j ∈ iterations g ⇒ stackInc i0 ≤ j`
        by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
      `i0 < stackInc i0` by metis_tac[ilistLT_stackInc] >>
      `i0 < i ∧ i0 ≠ i` by metis_tac[ilistLE_REFL, ilistLTE_trans] >>
      `i0 ∉ iterations g` by metis_tac[ilistLTE_trans, ilistLE_REFL] >>
      `ff i0 = i0' ∧ ff i = f i` by simp[Abbr`ff`] >> simp[] >>
      `∀j. j ∈ iterations g ⇒ ff j = f j` by (simp[Abbr`ff`] >> metis_tac[]) >>
      `INJ ff (i0 INSERT iterations g) UNIV`
        by (simp[INJ_INSERT] >> simp[Cong INJ_CONG] >>
            asm_simp_tac (srw_ss() ++ CONJ_ss ++ ETA_ss) [] >>
            fs[INJ_INSERT] >> qx_gen_tac `y` >> strip_tac >>
            `f y ∈ iterations (imap f g)` by simp[iterations_imap] >>
            `stackInc i0' ≤ f y`
              by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
            `i0' < stackInc i0'` by metis_tac[ilistLT_stackInc] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_add_action] >> simp[Cong imap_CONG] >>
      simp[readAction_def] >> simp[Once INJ_INSERT] >>
      asm_simp_tac (srw_ss() ++ CONJ_ss ++ DNF_ss) [] >>
      qx_gen_tac `y` >> fs[INJ_INSERT] >> Cases_on `y = i0` >> simp[] >>
      `stackInc i0' ≤ f i`
        by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
      `i0' < stackInc i0'` by metis_tac[ilistLT_stackInc] >>
      metis_tac[ilistLTE_trans, ilistLE_REFL])
  >- (rpt gen_tac >> strip_tac >> ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`,`m`,`dvs`,`g`] >> strip_tac >> fs[] >>
      qx_gen_tac `j` >> strip_tac >>
      first_x_assum (qspec_then `stackInc j` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `f` strip_assume_tac) >> simp[] >>
      qabbrev_tac `ff = λk. if k = i0 then j else f k` >> qexists_tac `ff` >>
      `i0 < stackInc i0 ∧ j < stackInc j ∧ stackInc i0 ≠ [] ∧ stackInc j ≠ []`
        by simp[] >>
      `(∀k. k ∈ iterations g ⇒ stackInc i0 ≤ k ∧ i0 < k) ∧ stackInc i0 ≤ i ∧
       i0 < i`
        by metis_tac[graphOf_iterations_apart, ilistLTE_trans, ilistLE_REFL]>>
      `i0 ∉ iterations g ∧ i0 ≠ i` by metis_tac[ilistLE_REFL] >>
      `ff i0 = j ∧ ff i = f i` by simp[Abbr`ff`] >>
      `∀k. k ∈ iterations g ⇒ ff k = f k` by (simp[Abbr`ff`] >> metis_tac[]) >>
      simp[] >>
      `INJ ff (i0 INSERT iterations g) UNIV`
        by (fs[INJ_INSERT, Cong INJ_CONG] >> csimp[] >> qx_gen_tac `y` >>
            strip_tac >> full_simp_tac (srw_ss() ++ ETA_ss) [] >>
            `f y ∈ iterations (imap f g)` by simp[iterations_imap] >>
            `stackInc (f y) ≤ f y`
              by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
            metis_tac[ilistLT_stackInc, stackInc_EQ_NIL,
                      ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_add_action] >> simp[Cong imap_CONG] >>
      Cases_on `d` >> simp[domreadAction_def] >> simp[Once INJ_INSERT] >>
      dsimp[] >> csimp[] >> fs[INJ_INSERT] >>
      `stackInc j ≤ f i`
        by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
      metis_tac[ilistLT_stackInc, ilistLTE_trans, ilistLE_REFL])
  >- ((* seq *)
      qx_gen_tac `cs` >> Cases_on `cs` >> simp[]
      >- (simp[graphOf_def] >> strip_tac >> qx_gen_tac `j` >> rpt strip_tac >>
          qexists_tac `\x. if x = i0 then j else ARB` >>
          simp[INJ_INSERT]) >>
      strip_tac >> ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m`, `i0'`, `m0'`, `g1`, `g2`] >>
      strip_tac >> qx_gen_tac `j` >> strip_tac >>
      `∃f1. graphOf j m0 h = SOME(f1 i0',m0',imap f1 g1) ∧ j = f1 i0 ∧
            INJ f1 (i0' INSERT iterations g1) UNIV`
        by metis_tac[] >> simp[] >>
      Q.UNDISCH_THEN `graphOf i0 m0 h = SOME(i0',m0',g1)`
        (fn th => first_x_assum
                    (fn impth => mp_tac (MATCH_MP impth th) >>
                                 assume_tac th)) >>
      simp[] >>
      first_x_assum (kall_tac o assert(is_forall o concl)) >>
      `i0' ≠ [] ∧ i0 ≤ i0' ∧ i0' ≤ i ∧ (∀k. k ∈ iterations g1 ⇒ k < i0') ∧
       ∀k. k ∈ iterations g2 ⇒ i0' ≤ k`
        by metis_tac[graphOf_iterations_apart, ilistLE_NIL] >>
      simp[] >>
      `DISJOINT (iterations g1) (iterations g2)`
        by (simp[DISJOINT_DEF, EXTENSION] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      disch_then (qspec_then `f1 i0'` mp_tac) >> simp[] >>
      `f1 i0' ≠ [] ∧ (∀k. k ∈ iterations (imap f1 g1) ⇒ k < f1 i0')`
        by metis_tac[graphOf_iterations_apart, ilistLE_NIL] >>
      simp[] >> disch_then (qx_choose_then `f2` strip_assume_tac) >>
      simp[] >>
      `∀k. k ∈ iterations (imap f2 g2) ⇒ f1 i0' ≤ k`
        by metis_tac[graphOf_iterations_apart] >>
      `INJ f1 (iterations g1) UNIV ∧ INJ f2 (iterations g2) UNIV`
        by fs[INJ_INSERT] >>
      qabbrev_tac `
        ff = λk. if k ∈ iterations g2 ∨ k = i then f2 k else f1 k` >>
      qexists_tac `ff` >>
      `f2 i = ff i` by simp[Abbr`ff`] >> simp[] >>
      `f1 i0 = ff i0`
        by (rw[Abbr`ff`] >> metis_tac[ilistLE_antisym]) >> simp[] >>
      `i ∉ iterations g1` by metis_tac[ilistLTE_trans, ilistLE_REFL] >>
      `(∀k. k ∈ iterations g1 ⇒ ff k = f1 k) ∧
       (∀k. k ∈ iterations g2 ⇒ ff k = f2 k)`
        by (simp[Abbr`ff`] >> qx_gen_tac `k` >> strip_tac >>
            `k ∉ iterations g2 ∧ k ≠ i`
              by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
            simp[]) >>
      `INJ ff (iterations g1 ∪ iterations g2) UNIV`
        by (simp[INJ_UNION_DOMAIN] >>
            `INJ ff (iterations g1) UNIV ∧ INJ ff (iterations g2) UNIV`
              by full_simp_tac (srw_ss() ++ ETA_ss)
                   [Cong INJ_CONG] >>
            `iterations g1 DIFF iterations g2 = iterations g1 ∧
             iterations g2 DIFF iterations g1 = iterations g2`
              by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
            simp[Cong (REWRITE_RULE [GSYM AND_IMP_INTRO] IMAGE_CONG)] >>
            CONV_TAC (DEPTH_CONV ETA_CONV) >>
            fs[iterations_imap, PULL_EXISTS] >>
            simp[DISJOINT_DEF, EXTENSION] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_merge_graph, Cong imap_CONG] >>
      simp[INJ_INSERT] >> dsimp[] >> reverse conj_tac
      >- (`∀k. k ∈ iterations (imap f2 g2) ⇒ k < ff i`
            by metis_tac[graphOf_iterations_apart] >> pop_assum mp_tac >>
          dsimp[iterations_imap] >> csimp[] >> metis_tac[ilistLE_REFL]) >>
      csimp[] >>
      `f2 i0' ≤ f2 i` by metis_tac[graphOf_iterations_apart] >>
      fs[iterations_imap, PULL_EXISTS] >>
      metis_tac[ilistLE_REFL, ilistLTE_trans])
  >- ((* parloop *)
      map_every qx_gen_tac [`vnm`, `d`, `body`] >>
      strip_tac >> ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m`, `dvs`, `g`] >> strip_tac >>
      qx_gen_tac `j` >> strip_tac >> fs[] >>
      first_x_assum (qspec_then `stackInc j` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `f` strip_assume_tac) >> simp[] >>
      qabbrev_tac `ff = λk. if k = i0 then j else f k` >> qexists_tac `ff` >>
      `i0 < stackInc i0 ∧ j < stackInc j ∧ stackInc i0 ≠ [] ∧ stackInc j ≠ []`
        by simp[] >>
      `(∀k. k ∈ iterations g ⇒ stackInc i0 ≤ k ∧ i0 < k) ∧ stackInc i0 ≤ i ∧
       i0 < i`
        by metis_tac[graphOf_iterations_apart, ilistLTE_trans, ilistLE_REFL]>>
      `i0 ∉ iterations g ∧ i0 ≠ i` by metis_tac[ilistLE_REFL] >>
      `ff i0 = j ∧ ff i = f i` by simp[Abbr`ff`] >>
      `∀k. k ∈ iterations g ⇒ ff k = f k` by (simp[Abbr`ff`] >> metis_tac[]) >>
      simp[] >>
      `INJ ff (i0 INSERT iterations g) UNIV`
        by (fs[INJ_INSERT, Cong INJ_CONG] >> csimp[] >> qx_gen_tac `y` >>
            strip_tac >> full_simp_tac (srw_ss() ++ ETA_ss) [] >>
            `f y ∈ iterations (imap f g)` by simp[iterations_imap] >>
            `stackInc (f y) ≤ f y`
              by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
            metis_tac[ilistLT_stackInc, stackInc_EQ_NIL,
                      ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_add_action] >> simp[Cong imap_CONG] >>
      Cases_on `d` >> simp[domreadAction_def] >> simp[Once INJ_INSERT] >>
      dsimp[] >> csimp[] >> fs[INJ_INSERT] >>
      `stackInc j ≤ f i`
        by metis_tac[graphOf_iterations_apart, stackInc_EQ_NIL] >>
      metis_tac[ilistLT_stackInc, ilistLTE_trans, ilistLE_REFL])
  >- ((* Par *)
      qx_gen_tac `cs` >> strip_tac >>
      ONCE_REWRITE_TAC [graphOf_def] >> simp[] >>
      simp[OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R, MEM_MAPi,
           PULL_EXISTS] >>
      qabbrev_tac `GG = λi0 i. graphOf (i0 ++ [i; 0]) m0` >> simp[] >>
      qabbrev_tac `
         TOS = λt:(num list # memory #
                   (value, actionRW, num list)action_graph) option.
               THE (OPTION_MAP (SND o SND) t)` >> simp[] >>
      qx_gen_tac `m` >> strip_tac >> qx_gen_tac `i0'` >> strip_tac >>
      fs[] >>
      `∃gfi gfm gfg.
         ∀n. n < LENGTH cs ⇒
             GG i0 n (EL n cs) = SOME (gfi n, gfm n, gfg n)`
        by (fs[EXISTS_PROD] >> metis_tac[]) >>
      first_x_assum (qspecl_then [`EL n cs`, `n`]
                                 (mp_tac o Q.GEN `n` o
                                  SIMP_RULE (srw_ss() ++ CONJ_ss)
                                            [EL_MEM])) >>
      simp[] >> simp[PULL_FORALL, SimpL ``(==>)``] >>
      disch_then (qspecl_then [`n`, `i0' ++ [n; 0]`]
                              (mp_tac o Q.GEN `n` o
                               SIMP_RULE (srw_ss()) [])) >>
      disch_then (mp_tac o
                  SIMP_RULE (srw_ss())
                            [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]) >>
      disch_then (qx_choose_then `ff` assume_tac) >>
      qabbrev_tac `
        fff = λi. if i = i0 then i0'
                  else if i = stackInc i0 then stackInc i0'
                  else ff (EL (LENGTH i0) i) i` >>
      qexists_tac `fff` >>
      `∀n. n < LENGTH cs ⇒ INJ (ff n) (iterations (gfg n)) UNIV`
        by metis_tac[INJ_INSERT]>>
      `∀n. n < LENGTH cs ⇒ ∃z. GG i0' n (EL n cs) = SOME z`
        by simp[Abbr`GG`] >> simp[] >>
      simp[Abbr`GG`, Abbr`TOS`] >> lfs[] >>
      `MAPi (λn c. THE (OPTION_MAP (SND o SND)
                                   (graphOf (i0 ++ [n;0]) m0 c))) cs =
       MAPi (λn c. gfg n) cs` by simp[LIST_EQ_REWRITE] >>
      simp[] >>
      `MAPi (λn c. THE (OPTION_MAP (SND o SND)
                                   (graphOf (i0' ++ [n;0]) m0 c))) cs =
       MAPi (λn c. imap (ff n) (gfg n)) cs`
        by simp[LIST_EQ_REWRITE] >>
      fs[] >> ntac 2 (pop_assum kall_tac) >>
      fs[FOLDR_MAPi, combinTheory.o_ABS_R] >>
      `∀n j. n < LENGTH cs ∧ j ∈ iterations (imap (ff n) (gfg n)) ⇒
             i0' ++ [n;0] ≤ j ∧
             TAKE (LENGTH (i0' ++ [n;0]) - 1) j = FRONT (i0' ++ [n;0])`
        by (rpt gen_tac >> strip_tac >> res_tac >>
            `i0' ++ [n;0] ≠ []` by simp[] >>
            metis_tac[graphOf_iterations_apart]) >>
      fs[FRONT_APPEND] >>
      `imap fff (FOLDRi (λn c. merge_graph (gfg n)) emptyG cs) =
       FOLDRi (λn c. merge_graph (imap fff (gfg n))) (imap fff emptyG) cs`
        by (ho_match_mp_tac imap_FOLDRi_merge >> simp[] >>
            `∀n. i0 ++ [n;0] ≠ []` by simp[] >>
            `∀n. FRONT (i0 ++ [n; 0]) = i0 ++ [n]`
              by simp[FRONT_APPEND] >>
            conj_tac
            >- (simp[DISJOINT_DEF, EXTENSION] >>
                map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
                qx_gen_tac `it` >> Cases_on `it ∈ iterations (gfg i)` >>
                simp[] >>
                `i < LENGTH cs` by decide_tac >> strip_tac >>
                `TAKE (LENGTH (i0 ++ [i;0]) - 1) it = i0 ++ [i] ∧
                 TAKE (LENGTH (i0 ++ [j;0]) - 1) it = i0 ++ [j]`
                  by metis_tac[graphOf_iterations_apart] >>
                fs[]) >>
            dsimp[iterations_FOLDRi_merge, INJ_THM] >>
            map_every qx_gen_tac [`it1`, `it2`, `i`, `j`] >> strip_tac >>
            `TAKE (LENGTH (i0 ++ [i;0]) - 1) it1 = i0 ++ [i] ∧
             TAKE (LENGTH (i0 ++ [j;0]) - 1) it2 = i0 ++ [j] ∧
             LENGTH (i0 ++ [i;0]) ≤ LENGTH it1 ∧
             LENGTH (i0 ++ [j;0]) ≤ LENGTH it2`
                by metis_tac[graphOf_iterations_apart] >>
            lfs[] >>
            `EL (LENGTH i0) it1 = EL (LENGTH i0) (i0 ++ [i]) ∧
             EL (LENGTH i0) it2 = EL (LENGTH i0) (i0 ++ [j])`
              by metis_tac[EL_TAKE,
                           DECIDE ``x < x + 1n``,
                           DECIDE ``x + 2n ≤ y ⇒ x + 1 ≤ y``] >>
            fs[EL_APPEND2] >>
            simp[Abbr`fff`] >>
            `it1 ≠ i0 ∧ it2 ≠ i0 ∧ it1 ≠ stackInc i0 ∧ it2 ≠ stackInc i0`
              by (rpt strip_tac >> lfs[]) >> simp[] >>
            reverse (Cases_on `i = j`)
            >- (`it1 ≠ it2` by (strip_tac >> fs[]) >> simp[] >>
                `ff i it1 ∈ iterations (imap (ff i) (gfg i)) ∧
                 ff j it2 ∈ iterations (imap (ff j) (gfg j))`
                  by simp[iterations_imap] >>
                `∀i. i < LENGTH cs ⇒ ff i (i0 ++ [i; 0]) ≠ []`
                  by metis_tac[APPEND_eq_NIL, NOT_CONS_NIL] >>
                `TAKE (LENGTH (i0' ++ [i;0]) - 1) (ff i it1) =
                 FRONT (i0' ++ [i;0]) ∧
                 TAKE (LENGTH (i0' ++ [j;0]) - 1) (ff j it2) =
                 FRONT (i0' ++ [j;0])`
                  by metis_tac[graphOf_iterations_apart] >>
                fs[FRONT_APPEND] >>
                strip_tac >> fs[]) >>
            pop_assum SUBST_ALL_TAC >> fs[INJ_THM]) >>
        `∀i. i < LENGTH cs ⇒ imap fff (gfg i) = imap (ff i) (gfg i)`
          by (pop_assum kall_tac >> simp[Abbr`fff`] >> qx_gen_tac `i` >>
              strip_tac >>
              match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] imap_CONG) >>
              simp[] >> qx_gen_tac `it` >> strip_tac >>
              `LENGTH (i0 ++ [i;0]) ≤ LENGTH it ∧
               TAKE (LENGTH (i0 ++ [i;0]) - 1) it = FRONT (i0 ++ [i;0])`
                by metis_tac[graphOf_iterations_apart, APPEND_eq_NIL,
                             NOT_CONS_NIL] >>
              `it ≠ i0 ∧ it ≠ stackInc i0` by (rpt strip_tac >> lfs[]) >>
              simp[] >> lfs[FRONT_APPEND] >>
              `EL (LENGTH i0) it = EL (LENGTH i0) (TAKE (LENGTH i0 + 1) it)`
                by simp[EL_TAKE] >>
              simp[EL_APPEND2]) >>
        fs[Cong FOLDRi_CONG] >> rpt conj_tac
        >- ((* eval result *) first_assum (SUBST1_TAC o SYM) >> simp[])
        >- simp[Abbr`fff`]
        >- simp[Abbr`fff`]
        >- ((* injectivity of fff *)
            asm_simp_tac (srw_ss() ++ ETA_ss ++ DNF_ss)
                         [INJ_INSERT, iterations_FOLDRi_merge] >>
            `∀i n. i ∈ iterations (gfg n) ∧ n < LENGTH cs ⇒
                   LENGTH (i0 ++ [n;0]) ≤ LENGTH i ∧
                   TAKE (LENGTH (i0 ++ [n;0]) - 1) i = FRONT (i0 ++ [n;0])`
              by metis_tac[APPEND_eq_NIL, NOT_CONS_NIL,
                           graphOf_iterations_apart] >>
            `∀i n. i ∈ iterations (gfg n) ∧ n < LENGTH cs ⇒
                   EL (LENGTH i0) i = n`
              by (rpt strip_tac >> lfs[FRONT_APPEND] >> res_tac >>
                  `EL (LENGTH i0) i =
                   EL (LENGTH i0) (TAKE (LENGTH i0 + 1) i)`
                    by simp[EL_TAKE] >> simp[EL_APPEND2]) >>
            reverse conj_tac
            >- (map_every qx_gen_tac [`y`, `n`] >> strip_tac >>
                qpat_assum `y ∈ iterations (gfg n)`
                  (fn i => qpat_assum `n < LENGTH cs`
                  (fn l => rpt (first_x_assum
                                  (strip_assume_tac o
                                   C MATCH_MP (CONJ i l))) >>
                           assume_tac i >> assume_tac l)) >>
                qpat_assum `fff (stackInc i0) = fff y` mp_tac >>
                simp[Abbr`fff`] >> lfs[FRONT_APPEND] >>
                `y ≠ i0 ∧ y ≠ stackInc i0` by (rpt strip_tac >> lfs[]) >>
                simp[] >>
                `ff n y ∈ iterations (imap (ff n) (gfg n))`
                  by simp[iterations_imap] >>
                `LENGTH (i0' ++ [n; 0]) ≤ LENGTH (ff n y)`
                  by metis_tac[graphOf_iterations_apart, NOT_CONS_NIL,
                               APPEND_eq_NIL] >>
                fs[] >> strip_tac >> `ff n y = stackInc i0'` by simp[] >>
                lfs[]) >>
            dsimp[INJ_DEF,Abbr`fff`] >>
            map_every qx_gen_tac [`it1`, `it2`, `i`, `j`] >>
            disch_then (CONJUNCTS_THEN
              (fn th => ASSUM_LIST (
                          map_every strip_assume_tac o
                          List.mapPartial (fn a =>
                               SOME (MATCH_MP a th)
                               handle HOL_ERR _ => NONE)) >>
                        strip_assume_tac th)) >>
            lfs[FRONT_APPEND] >>
            `it1 ≠ i0 ∧ it1 ≠ stackInc i0 ∧ it2 ≠ i0 ∧ it2 ≠ stackInc i0`
              by (rpt strip_tac >> lfs[]) >> simp[] >>
            Cases_on `i = j`
            >- (pop_assum SUBST_ALL_TAC >> metis_tac[INJ_DEF]) >>
            `it1 ≠ it2` by (strip_tac >> fs[]) >> simp[] >>
            `ff i it1 ∈ iterations (imap (ff i) (gfg i)) ∧
             ff j it2 ∈ iterations (imap (ff j) (gfg j))`
              by simp[iterations_imap] >>
            qpat_assum `imap fff ggg = XXX` kall_tac >>
            qpat_assum `∀i. i < LENGTH cs ⇒ imap fff ggg = g'g'g'` kall_tac >>
            `TAKE (LENGTH (i0' ++ [i;0]) - 1) (ff i it1) = FRONT (i0' ++ [i;0]) ∧
             TAKE (LENGTH (i0' ++ [j;0]) - 1) (ff j it2) = FRONT (i0' ++ [j;0])`
              by metis_tac[graphOf_iterations_apart, NOT_CONS_NIL,
                           APPEND_eq_NIL] >> lfs[FRONT_APPEND] >>
            strip_tac >> lfs[]))
  >- ((* assign *)
      csimp[graphOf_def, FORALL_PROD, PULL_EXISTS, INJ_INSERT,
            imap_add_action] >>
      rpt gen_tac >> strip_tac >> qx_gen_tac `j0` >>
      strip_tac >>
      qabbrev_tac `f =
        λi. if i = i0 then j0 else if i = isuc i0 then isuc j0
            else if i = isuc (isuc i0) then isuc (isuc j0)
            else isuc (isuc (isuc j0))` >>
      qexists_tac `f` >>
      `i0 < isuc i0 ∧ isuc i0 < isuc (isuc i0) ∧
       isuc (isuc i0) < isuc (isuc (isuc i0)) ∧
       j0 < isuc j0 ∧ isuc j0 < isuc (isuc j0) ∧
       isuc (isuc j0) < isuc (isuc (isuc j0))`
        by simp[ilistLT_stackInc] >>
      `i0 ≠ isuc i0 ∧ i0 ≠ isuc (isuc i0) ∧ i0 ≠ isuc (isuc (isuc i0)) ∧
       isuc j0 ≠ j0 ∧ j0 ≠ isuc (isuc j0) ∧ j0 ≠ isuc (isuc (isuc j0))`
        by metis_tac[ilistLT_trans, ilistLE_REFL] >> simp[] >>
      `f i0 = j0 ∧ f (isuc i0) = isuc j0 ∧
       f (isuc (isuc i0)) = isuc (isuc j0) ∧
       f (isuc (isuc (isuc i0))) = isuc (isuc (isuc j0))`
        by (simp[Abbr`f`]) >>
      simp[readAction_def] >>
      csimp[RIGHT_AND_OVER_OR, imap_add_action, INJ_INSERT, dvreadAction_def])
  >- ((* assign var *)
      csimp[graphOf_def, FORALL_PROD, PULL_EXISTS, INJ_INSERT,
            imap_add_action] >> rpt gen_tac >> strip_tac >> qx_gen_tac `j0` >>
      strip_tac >>
      qexists_tac `
        λi. if i = i0 then j0 else if i = stackInc i0 then stackInc j0
            else ARB` >> simp[])
  >- ((* Abort *) simp[graphOf_def])
  >- ((* Done *) csimp[graphOf_def, INJ_INSERT] >> strip_tac >>
      qx_gen_tac `j0` >> strip_tac >> qexists_tac `K j0` >> simp[])
  >- ((* Malloc *) simp[graphOf_def]))

val graphOf_simps = save_thm(
  "graphOf_simps[simp]",
  LIST_CONJ
    [ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 Done``,
     ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 Abort``,
     ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 (Malloc vn n v)``
    ]);

val isDValue_getReads = prove(
  ``EVERY isDValue rdes ⇒ ∃rds. getReads m0 rdes = SOME rds``,
  Induct_on `rdes` >> simp[getReads_def] >> Cases_on `h` >>
  simp[isDValue_def, getReads_def]);

val isDValue_destDValue = prove(
  ``EVERY isDValue rdes ⇒
    MAP THE (MAP (evalDexpr m0) rdes) = MAP destDValue rdes``,
  Induct_on `rdes` >> simp[] >> Cases_on `h` >>
  simp[isDValue_def, evalDexpr_def, destDValue_def]);

val _ = temp_overload_on ("lift2", ``OPTION_MAP2``)
val _ = temp_overload_on ("lift3", ``λf x y z. SOME f <*> x <*> y <*> z``)

val lift2_lift2_1 = prove(
  ``lift2 f x (lift2 g y z) = lift3 (λx y z. f x (g y z)) x y z``,
  map_every Cases_on [`x`, `y`, `z`] >> simp[]);

val lift2_lift2_2 = prove(
  ``lift2 f (lift2 g x y) z = lift3 (λx y z. f (g x y) z) x y z``,
  map_every Cases_on [`x`, `y`, `z`] >> simp[]);

val getReads_APPEND = store_thm(
  "getReads_APPEND",
  ``getReads m (l1 ++ l2) = OPTION_MAP2 (++) (getReads m l1) (getReads m l2)``,
  Induct_on `l1` >> simp[getReads_def]
  >- (Cases_on `getReads m l2` >> simp[]) >>
  Cases_on `h` >> simp[getReads_def, lift2_lift2_1, lift2_lift2_2] >>
  map_every Cases_on [`getReads m l1`, `getReads m l2`] >> simp[]);

val FOLDRi_APPEND = store_thm(
  "FOLDRi_APPEND",
  ``∀f. FOLDRi f a (l1 ++ l2) = FOLDRi f (FOLDRi (f o $+ (LENGTH l1)) a l2) l1``,
  Induct_on `l1` >> simp[]
  >- (gen_tac >> `f o $+ 0 = f` suffices_by simp[] >> simp[FUN_EQ_THM]) >>
  rpt gen_tac >>
  `f o SUC o $+ (LENGTH l1) = f o $+ (SUC (LENGTH l1))` suffices_by simp[] >>
  simp[FUN_EQ_THM, arithmeticTheory.ADD_CLAUSES]);

val pcg_eval_NONE = store_thm(
  "pcg_eval_NONE[simp]",
  ``∀g. pcg_eval g NONE = NONE``,
  ho_match_mp_tac graph_ind >> simp[pcg_eval_thm, apply_action_def] >>
  rpt gen_tac >> Cases_on `a.write` >> simp[]);

val expr_ind' = store_thm(
  "expr_ind'",
  ``∀P. (∀v. P (Value v)) ∧
        (∀f l. (∀e. MEM e l ⇒ P e) ⇒ P (Opn f l)) ∧
        (∀anm e. P e ⇒ P (ISub anm e)) ∧
        (∀s. P (VarExp s)) ⇒
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
  `a.write = NONE ∨ ∃w. a.write = SOME w` by (Cases_on `a.write` >> simp[]) >>
  simp[] >> pop_assum kall_tac >> gen_tac >>
  map_every qspec_tac [(`a.expr`, `expr`), (`a.reads`, `rds`), (`w`, `w`)] >>
  qid_spec_tac `e` >> ho_match_mp_tac expr_ind' >>
  simp[evalexpr_def, expr_reads_def] >> rpt conj_tac
  >- (simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
      AP_TERM_TAC >> simp[MAP_EQ_f] >> metis_tac[])
  >- (map_every qx_gen_tac [`anm`, `e`] >> strip_tac >>
      map_every qx_gen_tac [`w`, `rds`, `expr`, `m0`, `m`] >>
      strip_tac >>
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

val pcg_eval_expreval_preserves = store_thm(
  "pcg_eval_expreval_preserves",
  ``∀g m0 m.
       pcg_eval g (SOME m0) = SOME m ∧
       (∀a. a ∈ g ⇒ readAction j m0 e ≁ₜ a) ⇒
       evalexpr m e = evalexpr m0 e``,
  ho_match_mp_tac graph_ind >> simp[pcg_eval_thm] >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `apply_action a (SOME m0)` >> fs[] >>
  imp_res_tac apply_action_expr_eval_commutes >> metis_tac[]);

val apply_action_dvalues_commutes = store_thm(
  "apply_action_dvalues_commutes",
  ``apply_action a (SOME m0) = SOME m ∧ a ≁ₜ domreadAction i m0 d ⇒
    dvalues m d = dvalues m0 d ∧ domreadAction i m d = domreadAction i m0 d``,
  `∃e1 e2. d = D e1 e2` by (Cases_on `d` >> simp[]) >>
  simp[domreadAction_def, touches_def] >> strip_tac >>
  `a ≁ₜ readAction i m0 e1 ∧ a ≁ₜ readAction i m0 e2`
    by (simp[touches_def, readAction_def] >> metis_tac[]) >>
  `evalexpr m e1 = evalexpr m0 e1 ∧ readAction i m e1 = readAction i m0 e1 ∧
   evalexpr m e2 = evalexpr m0 e2 ∧ readAction i m e2 = readAction i m0 e2`
    by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
  simp[dvalues_def] >> fs[readAction_def, action_component_equality]);


val successful_action_diamond = store_thm(
  "successful_action_diamond",
  ``a1 ≁ₜ a2 ∧ apply_action a1 (SOME m0) = SOME m1 ∧
    apply_action a2 (SOME m0) = SOME m2 ⇒
    ∃m. apply_action a1 (SOME m2) = SOME m ∧
        apply_action a2 (SOME m1) = SOME m``,
  simp[apply_action_def, SimpL ``$==>``] >>
  `a1.write = NONE ∨ ∃w1. a1.write = SOME w1`
    by (Cases_on `a1.write` >> simp[]) >>
  `a2.write = NONE ∨ ∃w2. a2.write = SOME w2`
    by (Cases_on `a2.write` >> simp[]) >> simp[apply_action_def]
  >- (rw[] >> simp[]) >> strip_tac >> simp[] >> rw[] >>
  `MAP (lookupRW m2) a1.reads = MAP (lookupRW m0) a1.reads ∧
   MAP (lookupRW m1) a2.reads = MAP (lookupRW m0) a2.reads`
    by metis_tac[nontouching_updfs_expreval, touches_SYM] >>
  simp[] >>
  qmatch_rename_tac
    `∃m. updf w1 v1 m2 = SOME m ∧ updf w2 v2 m1 = SOME m` [] >>
  fs[touches_def] >>
  map_every (fn q => Q.UNDISCH_THEN q assume_tac)
    [`a1.write = SOME w1`, `a2.write = SOME w2`] >> fs[] >>
  metis_tac[successful_updf_diamond]);

val pcg_eval_apply_action_diamond = store_thm(
  "pcg_eval_apply_action_diamond",
  ``∀g m0 m1 a m2.
      pcg_eval g (SOME m0) = SOME m1 ∧
      apply_action a (SOME m0) = SOME m2 ∧
      (∀b. b ∈ g ⇒ a ≁ₜ b) ⇒
      ∃m. pcg_eval g (SOME m2) = SOME m ∧
          apply_action a (SOME m1) = SOME m``,
  ho_match_mp_tac graph_ind >>
  simp[pcg_eval_thm, DISJ_IMP_THM, FORALL_AND_THM] >>
  map_every qx_gen_tac [`b`, `g`] >> strip_tac >>
  map_every qx_gen_tac [`m0`, `m1`, `a`, `m2`] >> strip_tac >>
  `∃m0'. apply_action b (SOME m0) = SOME m0'`
    by (Cases_on `apply_action b (SOME m0)` >> fs[]) >>
  `∃mm. apply_action a (SOME m0') = SOME mm ∧
        apply_action b (SOME m2) = SOME mm`
    by metis_tac [successful_action_diamond] >> metis_tac[]);

val IN_FOLDRi_merge_graph = store_thm(
  "IN_FOLDRi_merge_graph",
  ``(∀i. i < LENGTH list ⇒
         DISJOINT (iterations (f i (EL i list))) (iterations acc)) ∧
    (∀i j. i < j ∧ j < LENGTH list ⇒
           DISJOINT (iterations (f i (EL i list)))
                    (iterations (f j (EL j list)))) ⇒
    (a ∈ FOLDRi (λn c. merge_graph (f n c)) acc list ⇔
     a ∈ acc ∨ ∃i. i < LENGTH list ∧ a ∈ f i (EL i list))``,
  qid_spec_tac `f` >>
  Induct_on `list` >> dsimp[combinTheory.o_ABS_L, LT_SUC] >>
  rw[EQ_IMP_THM] >> simp[]
  >- metis_tac[]
  >- (`a.iter ∈ iterations acc` by simp[iterations_thm] >>
      fs[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (`a.iter ∉ iterations (f 0 h)` suffices_by metis_tac[] >>
      `a.iter ∈ iterations (f (SUC n0) (EL n0 list))` by simp[iterations_thm] >>
      fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]))

val apply_action_dvreadAction_commutes = store_thm(
  "apply_action_dvreadAction_commutes",
  ``a ≁ₜ dvreadAction i m0 ds ∧ apply_action a (SOME m0) = SOME m ∧
    getReads m0 ds = SOME rds ∧
    (IS_SOME a.write ⇒ ¬MEM (THE a.write) rds)
   ⇒
    dvreadAction i m ds = dvreadAction i m0 ds ∧
    getReads m ds = getReads m0 ds ∧
    MAP (evalDexpr m) ds = MAP (evalDexpr m0) ds``,
  simp[dvreadAction_def, touches_def, MEM_FLAT, MEM_MAP, PULL_FORALL,
       GSYM IMP_DISJ_THM] >>
  `a.write = NONE ∨ ∃w. a.write = SOME w` by (Cases_on `a.write` >> simp[]) >>
  simp[FORALL_AND_THM, GSYM LEFT_FORALL_OR_THM, PULL_EXISTS,
       GSYM RIGHT_FORALL_OR_THM] >- csimp[apply_action_def] >>
  Cases_on `apply_action a (SOME m0) = SOME m` >> simp[] >>
  qid_spec_tac `rds` >> Induct_on `ds` >>
  simp[getReads_def] >> Cases >> simp[getReads_def, dvread_def, evalDexpr_def]
  >- (simp[dvread_def, DISJ_IMP_THM, FORALL_AND_THM] >> ntac 2 strip_tac >>
      `readAction i m0 e ≁ₜ a` by simp[readAction_def, touches_def] >>
      `readAction i m e = readAction i m0 e ∧ evalexpr m e = evalexpr m0 e`
        by metis_tac[apply_action_expr_eval_commutes] >>
      fs[readAction_def] >> BasicProvers.VAR_EQ_TAC >> fs[] >>
      qmatch_assum_rename_tac `w ≠ Array anm i : actionRW` [] >>
      imp_res_tac some_EQ_SOME_E >> fs[] >>
      `evalexpr m0 (ISub anm e) = lookup_array m0 anm i ∧
       evalexpr m (ISub anm e) = lookup_array m anm i`
        by simp[evalexpr_def] >>
      `a ≁ₜ readAction jj m0 (ISub anm e)`
        by simp[readAction_def, touches_def, expr_reads_def] >>
      metis_tac[apply_action_expr_eval_commutes, touches_SYM]) >>
  simp[dvread_def, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
  qx_gen_tac `z` >> strip_tac >>
  qmatch_assum_rename_tac `w ≠ Variable v` [] >>
  `evalexpr m0 (VarExp v) = lookup_v m0 v ∧
   evalexpr m (VarExp v) = lookup_v m v`
    by simp[evalexpr_def] >>
  `a ≁ₜ readAction jj m0 (VarExp v)`
    by simp[touches_def, readAction_def, expr_reads_def] >>
  metis_tac[apply_action_expr_eval_commutes, touches_SYM])

val graphOf_apply_action_diamond = store_thm(
  "graphOf_apply_action_diamond",
  ``∀i0 m0 c i m1 m2 a g.
      graphOf i0 m0 c = SOME(i,m1,g) ∧ i0 ≠ [] ∧
      apply_action a (SOME m0) = SOME m2 ∧
      (∀b. b ∈ g ⇒ a ≁ₜ b) ⇒
      ∃m.
        graphOf i0 m2 c = SOME(i,m,g) ∧
        apply_action a (SOME m1) = SOME m``,
  ho_match_mp_tac (theorem "graphOf_ind") >> rpt conj_tac >>
  map_every qx_gen_tac [`i0`, `m0`]
  >- ((* if *)
      qx_gen_tac `gd` >> rpt gen_tac >> strip_tac >> simp[graphOf_def] >>
      rpt gen_tac >>
      Cases_on `evalexpr m0 gd` >> simp[] >>
      qmatch_assum_rename_tac `evalexpr m0 gd = Bool b` [] >>
      Cases_on `b` >> fs[] >> simp[PULL_EXISTS, EXISTS_PROD] >>
      qx_gen_tac `g'` >> rw[] >>
      `i0 ∉ iterations g'`
        by metis_tac[ilistLT_stackInc, ilistLTE_trans,
                     stackInc_EQ_NIL, ilistLE_REFL, graphOf_iterations_apart] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `evalexpr m2 gd = evalexpr m0 gd ∧
       readAction i0 m2 gd = readAction i0 m0 gd`
        by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
      simp[EXISTS_PROD] >> metis_tac[])
  >- (map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      ONCE_REWRITE_TAC [graphOf_def] >> simp[PULL_EXISTS, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `dvs`, `g`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `i0 ∉ iterations g`
        by metis_tac[ilistLT_stackInc, ilistLTE_trans,
                     stackInc_EQ_NIL, ilistLE_REFL, graphOf_iterations_apart] >>
      `dvalues m2 d = dvalues m0 d ∧ domreadAction i0 m2 d = domreadAction i0 m0 d`
        by metis_tac[apply_action_dvalues_commutes] >>
      simp[] >> metis_tac[])
  >- ((* seq *) qx_gen_tac `cmds` >> Cases_on `cmds` >> simp[]
      >- simp[graphOf_def] >> strip_tac >> ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, EXISTS_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
      map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `i1`, `m0'`, `g1`, `g2`] >>
      strip_tac >> fs[] >>
      qmatch_assum_rename_tac `graphOf i0 m0 c1 = SOME(i1,m0',g1)` [] >>
      `∃m1'. graphOf i0 m2 c1 = SOME(i1,m1',g1) ∧
             apply_action a (SOME m0') = SOME m1'` by metis_tac[] >>
      simp[] >>
      `i1 ≠ []` by metis_tac[graphOf_iterations_apart, LENGTH_NIL] >>
      `∀b. b ∈ g2 ⇒ b.iter ∉ iterations g1`
        by (gen_tac >> strip_tac >>
            `b.iter ∈ iterations g2` by simp[iterations_thm] >>
            metis_tac[graphOf_iterations_apart, ilistLTE_trans, ilistLE_REFL])>>
      full_simp_tac (srw_ss() ++ CONJ_ss) [] >>
      metis_tac[])
  >- ((* parloop *)
      map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      ONCE_REWRITE_TAC [graphOf_def] >> simp[PULL_EXISTS, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `dvs`, `g`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `i0 ∉ iterations g`
        by metis_tac[ilistLT_stackInc, ilistLTE_trans,
                     stackInc_EQ_NIL, ilistLE_REFL, graphOf_iterations_apart] >>
      `dvalues m2 d = dvalues m0 d ∧
       domreadAction i0 m2 d = domreadAction i0 m0 d`
        by metis_tac[apply_action_dvalues_commutes] >>
      simp[] >> metis_tac[])
  >- ((* par *)
      qx_gen_tac `cmds` >> strip_tac >> map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `g`] >>
      ONCE_REWRITE_TAC [graphOf_def] >>
      simp[OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R, MEM_MAPi, PULL_EXISTS] >>
      qabbrev_tac `TOS = λt:(num list # memory #
                                 (value, actionRW, num list)action_graph) option.
                            THE (OPTION_MAP (SND o SND) t)` >> simp[] >>
      simp[FOLDR_MAPi, combinTheory.o_ABS_R] >> fs[] >> strip_tac >> fs[] >>
      csimp[] >>
      `∃m. pcg_eval g (SOME m2) = SOME m ∧ apply_action a (SOME m1) = SOME m`
        by metis_tac[pcg_eval_apply_action_diamond] >> simp[] >>
      qabbrev_tac `GG = λi. graphOf (i0 ++ [i;0])` >> simp[] >>
      `∀it j. j < LENGTH cmds ∧ it ∈ iterations (TOS (GG j m0 (EL j cmds))) ⇒
              EL (LENGTH i0) it = j`
        by (rpt strip_tac >>
            `∃j' m' g'. graphOf (i0 ++ [j;0]) m0 (EL j cmds) = SOME (j',m',g')`
              by (fs[EXISTS_PROD] >> metis_tac[]) >>
            `TOS (GG j m0 (EL j cmds)) = g'` by simp[Abbr`GG`, Abbr`TOS`] >>
            `∀k. k ∈ iterations g' ⇒
                 LENGTH (i0 ++ [j;0]) ≤ LENGTH k ∧
                 TAKE (LENGTH (i0 ++ [j;0]) - 1) k = FRONT (i0 ++ [j;0])`
              by metis_tac[APPEND_eq_NIL, NOT_CONS_NIL,
                           graphOf_iterations_apart] >>
            lfs[FRONT_APPEND] >> pop_assum (qspec_then `it` mp_tac) >>
            simp[] >> strip_tac >>
            `EL (LENGTH i0) it = EL (LENGTH i0) (TAKE (LENGTH i0 + 1) it)`
              by simp[EL_TAKE] >> simp[EL_APPEND2]) >>
      `∀b. b ∈ g ⇔
           b ∈ emptyG ∨
           ∃i. i < LENGTH cmds ∧ b ∈ TOS (graphOf (i0 ++ [i;0]) m0 (EL i cmds))`
        by (RW_TAC bool_ss [] >> ho_match_mp_tac IN_FOLDRi_merge_graph >>
            simp[] >> simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
            spose_not_then strip_assume_tac >>
            qmatch_assum_rename_tac
              `iter ∈ iterations (TOS (GG i m0 (EL i cmds)))` [] >>
            `i < LENGTH cmds ∧ i ≠ j` by decide_tac >> metis_tac[]) >>
      fs[PULL_EXISTS] >>
      `∀n. n < LENGTH cmds ⇒ ∃z. graphOf (i0 ++ [n;0]) m2 (EL n cmds) = SOME z`
        by (rpt strip_tac >>
            `∃z. graphOf (i0 ++ [n;0]) m0 (EL n cmds) = SOME z` by metis_tac[] >>
            PairCases_on `z` >> `MEM (EL n cmds) cmds` by metis_tac[MEM_EL] >>
            simp[EXISTS_PROD] >>
            first_x_assum (qspecl_then [`EL n cmds`, `n`] mp_tac) >> simp[] >>
            simp[Abbr`GG`] >> fs[] >>
            disch_then (qspecl_then [`m2`, `a`] mp_tac) >> simp[] >>
            qpat_assum `∀b i. i < LENGTH cmds ∧ PP ⇒ a ≁ₜ b`
              (qspec_then `n` mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
            simp[Abbr`TOS`] >> metis_tac[]) >>
      conj_tac >- simp[Abbr`GG`] >>
      `∀i. i < LENGTH cmds ⇒
           TOS (GG i m2 (EL i cmds)) = TOS (GG i m0 (EL i cmds))`
        suffices_by
        (simp[] >> rw[] >> match_mp_tac FOLDRi_CONG' >> simp[]) >>
      qx_gen_tac `j` >> strip_tac >>
      first_x_assum (qspecl_then [`EL j cmds`, `j`] mp_tac) >>
      simp[EL_MEM] >>
      `∃it m' g'. graphOf (i0 ++ [j; 0]) m0 (EL j cmds) = SOME(it,m',g')`
        by (fs[EXISTS_PROD] >> metis_tac[]) >> pop_assum mp_tac >>
      simp[] >> strip_tac >> disch_then (qspecl_then [`m2`, `a`] mp_tac) >>
      simp[] >>
      qpat_assum `∀b i. i < LENGTH cmds ∧ PP ⇒ a ≁ₜ b`
       (qspec_then `j` mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
      simp[Abbr`TOS`] >> rpt strip_tac >> simp[])
  >- ((* assign *)
      simp[graphOf_def, FORALL_PROD, PULL_EXISTS] >>
      map_every qx_gen_tac [`anm`, `i_e`, `ds`, `opn`, `m1`, `m2`, `a`, `iv`,
                            `rds`, `rvs`] >> strip_tac >>
      pop_assum mp_tac >> dsimp[] >> strip_tac >>
      `readAction i0 m2 i_e = readAction i0 m0 i_e ∧
       evalexpr m2 i_e = evalexpr m0 i_e`
        by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
      simp[] >>
      `IS_SOME a.write ⇒ ¬MEM (THE a.write) rds`
        by (Cases_on `a.write` >> fs[touches_def]) >>
      `getReads m2 ds = getReads m0 ds ∧
       dvreadAction (isuc i0) m2 ds = dvreadAction (isuc i0) m0 ds ∧
       MAP (evalDexpr m2) ds = MAP (evalDexpr m0) ds`
        by metis_tac[apply_action_dvreadAction_commutes] >> simp[] >>
      qabbrev_tac `b = <| reads := []; write := SOME(Array anm iv);
                          expr := K (opn rvs); iter := xx|>` >>
      `∀m. upd_array m anm iv (opn rvs) = apply_action b (SOME m)`
        by simp[apply_action_def, Abbr`b`, updf_def] >> fs[] >>
      `a ≁ₜ b` by (simp[touches_def, Abbr`b`] >> fs[touches_def] >>
                  Cases_on `a.write` >> fs[]) >>
      metis_tac[successful_action_diamond])
  >- ((* assignvar *)
      simp[graphOf_def] >>
      map_every qx_gen_tac [`vnm`, `e`, `m1`, `m2`, `a`] >>
      strip_tac >>
      `readAction jj m0 e ≁ₜ a`
        by (fs[readAction_def, touches_def] >> metis_tac[]) >>
      `evalexpr m2 e = evalexpr m0 e ∧
       readAction jj m2 e = readAction jj m0 e`
        by metis_tac[apply_action_expr_eval_commutes] >>
      fs[readAction_def] >>
      qabbrev_tac `b = <| reads := []; write := SOME (Variable vnm);
                          expr := K (evalexpr m0 e); iter := jj |>` >>
      `∀m. updf (Variable vnm) (evalexpr m0 e) m = apply_action b (SOME m)`
        by simp[apply_action_def, Abbr`b`] >> fs[] >>
      `a ≁ₜ b` by (fs[Abbr`b`, touches_def] >> metis_tac[]) >>
      metis_tac[successful_action_diamond])
  >- ((* abort *) simp[graphOf_def])
  >- ((* Done *) simp[graphOf_def])
  >- ((* malloc *) simp[graphOf_def]))

val graphOf_pcg_eval_diamond = store_thm(
  "graphOf_pcg_eval_diamond",
  ``∀g1 m0 m1 i c i' m2 g2.
      pcg_eval g1 (SOME m0) = SOME m1 ∧ i ≠ [] ∧
      graphOf i m0 c = SOME(i',m2,g2) ∧
      ¬gtouches g1 g2 ⇒
      ∃m2'. graphOf i m1 c = SOME(i',m2',g2) ∧
            pcg_eval g1 (SOME m2) = SOME m2'``,
  ho_match_mp_tac graph_ind >> simp[pcg_eval_thm] >> rpt strip_tac >>
  `∀b. b ∈ g2 ⇒ a ≁ₜ b` by metis_tac[] >>
  `∃m0'. apply_action a (SOME m0) = SOME m0'`
    by (Cases_on `apply_action a (SOME m0)` >> fs[]) >>
  `∃mm. apply_action a (SOME m2) = SOME mm ∧
        graphOf i m0' c = SOME(i',mm,g2)`
    by metis_tac[graphOf_apply_action_diamond, touches_SYM] >>
  metis_tac[]);

val pregraph_def = Define`
  pregraph a G = ITSET (λb g. g \\ b) { b | b ∈ G ∧ b -<G>/-> a } G
`;

val pregraph_emptyG = store_thm(
  "pregraph_emptyG[simp]",
  ``pregraph a emptyG = emptyG``,
  simp[pregraph_def, ITSET_EMPTY]);

val ITSET_gDELETE_ALL = store_thm(
  "ITSET_gDELETE_ALL",
  ``∀g. ITSET (λb g. g \\ b) (ag_nodes g) g = emptyG``,
  ho_match_mp_tac graph_ind >> simp[ITSET_EMPTY] >>
  map_every qx_gen_tac [`a`, `g`] >> strip_tac >>
  `ag_nodes (a ⊕ g) = a INSERT ag_nodes g` by simp[EXTENSION] >>
  simp[] >>
  `(a ⊕ g) \\ a = g`
    by (simp[graph_equality, add_action_edges] >> metis_tac[IN_edges]) >>
  `ITSET (λb g. g \\ b) (a INSERT ag_nodes g) (a ⊕ g) =
   ITSET (λb g. g \\ b) (ag_nodes g DELETE a) ((λb g. g \\ b) a (a ⊕ g))`
    suffices_by simp[DELETE_NON_ELEMENT_RWT] >>
  match_mp_tac COMMUTING_ITSET_INSERT >> simp[gDELETE_commutes]);

val pregreph_add_action_id = store_thm(
  "pregreph_add_action_id[simp]",
  ``a.iter ∉ iterations g ⇒ pregraph a (a ⊕ g) = emptyG``,
  dsimp[pregraph_def, add_action_edges] >> csimp[] >> strip_tac >>
  `a ∉ g` by (strip_tac >> fs[iterations_thm]) >>
  simp[] >>
  qmatch_abbrev_tac `ITSET (λb g. g \\ b) ss (a ⊕ g) = emptyG` >>
  `ss = ag_nodes (a ⊕ g)`
    by (simp[Abbr`ss`, EXTENSION] >> qx_gen_tac `e` >> eq_tac >> strip_tac >>
        simp[] >> `e ≠ a` by metis_tac [] >> simp[] >>
        metis_tac[IN_edges]) >>
  simp[ITSET_gDELETE_ALL]);

val pregraph_absent = store_thm(
  "pregraph_absent",
  ``b ∉ g ⇒ pregraph b g = emptyG``,
  simp[pregraph_def] >> strip_tac >>
  `∀a. a -<g>/-> b` by metis_tac[IN_edges] >>
  simp[ITSET_gDELETE_ALL]);

val pregraph_subset = store_thm(
  "pregraph_subset",
  ``∀g b. b ∈ pregraph a g ⇒ b ∈ g``,
  simp[pregraph_def] >> rpt gen_tac >>
  `∀s. FINITE s ⇒ ∀g. b ∈ ITSET (λb g. g \\ b) s g ⇒ b ∈ g`
    suffices_by (disch_then match_mp_tac >>
                 match_mp_tac SUBSET_FINITE_I >>
                 qexists_tac `ag_nodes g` >> simp[SUBSET_DEF]) >>
  Induct_on `FINITE s` >>
  simp[ITSET_EMPTY, gDELETE_commutes, COMMUTING_ITSET_INSERT,
       DELETE_NON_ELEMENT_RWT] >> rpt strip_tac >>
  res_tac >> fs[]);

val ITSET_DEL = prove(
  ``∀s. FINITE s ⇒ ∀g a. a ∉ s ∧ a.iter ∉ iterations g ⇒
        ITSET (λb g. g \\ b) s (a ⊕ g) = a ⊕ ITSET (λb g. g \\ b) s g``,
  Induct_on `FINITE s` >>
  simp[ITSET_EMPTY, COMMUTING_ITSET_INSERT, gDELETE_commutes,
       DELETE_NON_ELEMENT_RWT] >>
  rpt strip_tac >>
  `a.iter ∉ iterations (g \\ e)` by (fs[iterations_thm] >> metis_tac[]) >>
  `(a ⊕ g) \\ e = a ⊕ (g \\ e)` suffices_by simp[] >>
  simp[graph_equality, add_action_edges, EQ_IMP_THM] >> rpt strip_tac >>
  simp[] >> metis_tac[]);

val pregraph_add_action_1 = prove(
  ``a.iter ∉ iterations g ∧ a ≠ b ∧ b ∈ g ∧ a ∼ₜ b ⇒
    pregraph b (a ⊕ g) = a ⊕ pregraph b g``,
  simp[pregraph_def, add_action_edges] >> dsimp[] >> csimp[] >>
  strip_tac >>
  qmatch_abbrev_tac `ITSET del s1 (a ⊕ g) = a ⊕ ITSET del s2 g` >>
  `a ∉ g` by (strip_tac >> fs[iterations_thm]) >>
  `s1 = s2`
    by dsimp[EXTENSION, Abbr`s1`, Abbr`s2`, EQ_IMP_THM] >>
  simp[Abbr`del`] >> `FINITE s2 ∧ a ∉ s2` suffices_by metis_tac[ITSET_DEL] >>
  rpt strip_tac
  >- (match_mp_tac SUBSET_FINITE_I >> qexists_tac `ag_nodes g` >>
      simp[SUBSET_DEF, Abbr`s2`]) >>
  qunabbrev_tac `s2` >> fs[]);

val pregraph_add_action_2 = prove(
  ``a.iter ∉ iterations g ∧ a ≠ b ∧ b ∈ g ∧ a ≁ₜ b ⇒
    pregraph b (a ⊕ g) = pregraph b g``,
  simp[pregraph_def, add_action_edges] >> rpt strip_tac >>
  `a ∉ g` by (strip_tac >> fs[iterations_thm]) >>
  qmatch_abbrev_tac `ITSET del s1 (a ⊕ g) = ITSET del s2 g` >>
  `s1 = a INSERT s2`
    by (dsimp[EXTENSION, Abbr`s1`, Abbr`s2`, EQ_IMP_THM] >> csimp[] >>
        metis_tac[IN_edges]) >>
  `FINITE s2`
    by (match_mp_tac SUBSET_FINITE_I >> qexists_tac `ag_nodes g` >>
        simp[SUBSET_DEF, Abbr`s2`]) >>
  `a ∉ s2` by simp[Abbr`s2`] >>
  simp[Abbr`del`, COMMUTING_ITSET_INSERT, gDELETE_commutes,
       DELETE_NON_ELEMENT_RWT] >>
  `(a ⊕ g) \\ a = g` suffices_by simp[] >>
  simp[graph_equality, add_action_edges] >> metis_tac[IN_edges])

val pregraph_add_action = store_thm(
  "pregraph_add_action",
  ``a.iter ∉ iterations g ⇒
    pregraph b (a ⊕ g) =
      if b ∈ g then
        (if a ∼ₜ b then add_action a else I)
        (pregraph b g)
      else emptyG``,
  strip_tac >> `a ∉ g` by (strip_tac >> fs[iterations_thm]) >>
  rw[]
  >- (`a ≠ b` by (strip_tac >> fs[]) >>
      simp[pregraph_add_action_1])
  >- (`a ≠ b` by (strip_tac >> fs[]) >>
      simp[pregraph_add_action_2]) >>
  Cases_on `a = b` >> rw[] >>
  simp[pregraph_absent]);

val pregraph_add_postaction = store_thm(
  "pregraph_add_postaction",
  ``∀g a. a ∈ g ⇒ pregraph a (add_postaction b g) = pregraph a g``,
  ho_match_mp_tac graph_ind >> dsimp[] >> conj_tac
  >- (map_every qx_gen_tac [`a`, `g`] >> strip_tac >>
      Cases_on `a.iter = b.iter` >- simp[add_postactionID] >>
      simp[add_action_add_postaction_ASSOC]) >>
  map_every qx_gen_tac [`a`, `g`, `c`] >> rpt strip_tac >>
  Cases_on `a.iter = b.iter` >- simp[add_postactionID] >>
  simp[add_action_add_postaction_ASSOC, pregraph_add_action]);

val pregraph_merge_graph = store_thm(
  "pregraph_merge_graph",
  ``∀g2 g1 a. a ∈ g1 ⇒ pregraph a (merge_graph g1 g2) = pregraph a g1``,
  ho_match_mp_tac graph_ind >> dsimp[merge_graph_thm, pregraph_add_postaction]);

val IN_FOLDRi_merge_graph' =
    IN_FOLDRi_merge_graph |> Q.INST [`acc` |-> `emptyG`]
                          |> SIMP_RULE (srw_ss()) []

val pregraph_FOLDRi_merge_graph = store_thm(
  "pregraph_FOLDRi_merge_graph",
  ``∀list n f.
      n < LENGTH list ∧ a ∈ f n (EL n list) ∧
      (∀i j. i < j ∧ j < LENGTH list ⇒
             ¬gtouches (f i (EL i list)) (f j (EL j list)) ∧
             DISJOINT (iterations (f i (EL i list)))
                      (iterations (f j (EL j list)))) ⇒
      pregraph a (FOLDRi (λn c. merge_graph (f n c)) emptyG list) =
      pregraph a (f n (EL n list))``,
  Induct >> dsimp[LT_SUC, combinTheory.o_ABS_L] >> conj_tac
  >- simp[pregraph_merge_graph] >>
  map_every qx_gen_tac [`h`, `f`, `n`] >> strip_tac >>
  first_x_assum (qspecl_then [`n`, `f o SUC`] mp_tac) >> simp[] >>
  strip_tac >>
  qmatch_abbrev_tac `pregraph a (merge_graph g1 g2) = pregraph a g3` >>
  `a ∈ g2`
    by (simp[IN_FOLDRi_merge_graph, Abbr`g2`] >> metis_tac[]) >>
  `merge_graph g1 g2 = merge_graph g2 g1` suffices_by
    (disch_then SUBST1_TAC >> simp[pregraph_merge_graph]) >>
  match_mp_tac nontouching_merge_COMM >>
  dsimp[iterations_FOLDRi_merge, Abbr`g2`] >>
  simp[gtouches_def, IN_FOLDRi_merge_graph] >>
  metis_tac[gtouches_def]);

val eval_graphOf_action = store_thm(
  "eval_graphOf_action",
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      m0 ≠ m ⇒
      ∀i0 i0' m0' g0.
        i0 ≠ [] ∧ graphOf i0 m0 c0 = SOME(i0', m0', g0) ⇒
        ∃a. a ∈ g0 ∧ (∀b. b ∈ pregraph a g0 ⇒ b.write = NONE) ∧
            apply_action a (SOME m0) = SOME m``,
  ho_match_mp_tac eval_ind' >> rpt conj_tac >> REWRITE_TAC []
  >- ((* head of Seq steps *)
      rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
      rpt gen_tac >> simp[Once graphOf_def] >>
      simp[EXISTS_PROD, PULL_EXISTS] >>
      map_every qx_gen_tac [`ci`, `cm`, `cg`, `rg`] >>
      strip_tac >> rw[] >>
      `∃a. a ∈ cg ∧ (∀b. b ∈ pregraph a cg ⇒ b.write = NONE) ∧
           apply_action a (SOME m0) = SOME m`
        by metis_tac[] >>
      qexists_tac `a` >> simp[pregraph_merge_graph])
  >- ((* assignvar *)
      simp[graphOf_def] >> simp[apply_action_def, updf_def])
  >- ((* assign *)
      simp[graphOf_def, PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      rpt strip_tac >> dsimp[] >> disj2_tac >>
      simp[apply_action_def, updf_def, mergeReads_def] >>
      reverse conj_tac
      >- (imp_res_tac assign_lemma >> simp[] >>
          fs[OPT_SEQUENCE_EQ_SOME, evalexpr_def] >> rw[] >>
          imp_res_tac isDValue_destDValue >> fs[]) >>
      simp[pregraph_add_action] >>
      simp[touches_def, readAction_def, expr_reads_def, dvreadAction_def] >>
      rw[])
  >- ((* par *)
      map_every qx_gen_tac [`m0`, `m`, `pfx`, `c0`, `c`, `sfx`] >> strip_tac >>
      strip_tac >> fs[] >> simp[Once graphOf_def] >>
      simp[PULL_EXISTS, OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R] >>
      qabbrev_tac `
        TOS = λt:(num list # memory #
                  (value, actionRW, num list)action_graph) option.
               THE (OPTION_MAP (SND o SND) t)` >> simp[] >>
      map_every qx_gen_tac [`i0`, `m'`] >>
      qabbrev_tac `GG = λn. graphOf (i0 ++ [n;0])` >> simp[] >>
      simp[FOLDR_MAPi, combinTheory.o_ABS_R, MEM_MAPi, PULL_EXISTS] >>
      strip_tac >>
      first_x_assum (qx_choosel_then [`gi`, `gm`, `gg`] assume_tac o
                     SIMP_RULE (srw_ss()) [EXISTS_PROD,
                                           GSYM RIGHT_EXISTS_IMP_THM,
                                           SKOLEM_THM]) >>
      `∀x y z. TOS (SOME (x,y,z)) = z` by simp[Abbr`TOS`] >>
      lfs[] >>
      `∀i j. i < j ∧ j < LENGTH pfx + (LENGTH sfx + 1) ⇒
             DISJOINT (iterations (gg i)) (iterations (gg j))`
        by (map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
            first_x_assum (fn th =>
              map_every (fn q => qspec_then q mp_tac th) [`i`, `j`]) >>
            simp[Abbr`GG`] >> rpt strip_tac >>
            `(∀it. it ∈ iterations (gg i) ⇒
                   TAKE (LENGTH (i0 ++ [i;0]) - 1) it = FRONT (i0 ++ [i;0])) ∧
             (∀it. it ∈ iterations (gg j) ⇒
                   TAKE (LENGTH (i0 ++ [j;0]) - 1) it = FRONT (i0 ++ [j;0]))`
              by metis_tac[graphOf_iterations_apart, APPEND_eq_NIL] >>
            lfs[FRONT_APPEND] >> `i0 ++ [i] ≠ i0 ++ [j]` by simp[] >>
            simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      simp[IN_FOLDRi_merge_graph] >>
      first_x_assum (qspecl_then [`i0 ++ [LENGTH pfx; 0]`,
                                  `gi (LENGTH pfx)`,
                                  `gm (LENGTH pfx)`,
                                  `gg (LENGTH pfx)`] mp_tac) >>
      simp[] >> csimp[] >>
      `LENGTH pfx < LENGTH pfx + (LENGTH sfx + 1)` by decide_tac >>
      pop_assum (fn th => first_assum (mp_tac o C MATCH_MP th)) >>
      simp_tac (srw_ss() ++ ARITH_ss) [EL_APPEND2, EL_APPEND1] >>
      disch_then kall_tac >> disch_then (qx_choose_then `a` strip_assume_tac) >>
      qexists_tac `a` >> conj_tac >- (qexists_tac `LENGTH pfx` >> simp[]) >>
      simp[] >>
      Q.ISPEC_THEN `pfx ++ [c0] ++ sfx`
        (Q.ISPEC_THEN `LENGTH pfx`
           (Q.ISPEC_THEN `λn c. TOS (GG n m0 c)` mp_tac))
        pregraph_FOLDRi_merge_graph >> simp[]))

val gtouches_SYM = store_thm(
  "gtouches_SYM",
  ``gtouches g1 g2 ⇒ gtouches g2 g1``,
  metis_tac[gtouches_def, touches_SYM]);

val MAPi_APPEND = store_thm(
  "MAPi_APPEND",
  ``∀l1 l2 f. MAPi f (l1 ++ l2) = MAPi f l1 ++ MAPi (f o (+) (LENGTH l1)) l2``,
  Induct >> simp[] >> rpt gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]);

val MAPi_GENLIST = store_thm(
  "MAPi_GENLIST",
  ``∀l f. MAPi f l = GENLIST (S f (combin$C EL l)) (LENGTH l)``,
  Induct >> simp[GENLIST_CONS] >> rpt gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[FUN_EQ_THM]);

val GENLIST_CONG = store_thm(
  "GENLIST_CONG",
  ``(∀m. m < n ⇒ f1 m = f2 m) ⇒ GENLIST f1 n = GENLIST f2 n``,
  map_every qid_spec_tac [`f1`, `f2`] >> Induct_on `n` >>
  simp[GENLIST_CONS]);

val _ = temp_overload_on ("MergeL", ``FOLDR merge_graph emptyG``)

val FOLDR_merge_lemma = prove(
  ``(∀g. MEM g l1 ⇒ ¬gtouches g e ∧ DISJOINT (iterations g) (iterations e)) ⇒
    FOLDR merge_graph emptyG (l1 ++ [e] ++ l2) =
    merge_graph e (FOLDR merge_graph emptyG (l1 ++ l2))``,
  Induct_on `l1` >> dsimp[merge_graph_ASSOC] >>
  metis_tac[nontouching_merge_COMM])

val pcg_eval_merge_graph' = prove(
  ``DISJOINT (iterations g1) (iterations g2) ⇒
    pcg_eval (merge_graph g1 g2) = pcg_eval g2 o pcg_eval g1``,
  simp[FUN_EQ_THM] >> rpt strip_tac >>
  match_mp_tac pcg_eval_merge_graph >>
  fs[DISJOINT_DEF, EXTENSION, iterations_thm] >>
  metis_tac[]);

val iterations_MergeL = prove(
  ``iterations (MergeL l) = BIGUNION (IMAGE iterations (set l))``,
  dsimp[Once EXTENSION, iterations_FOLDR_merge_graph] >>
  metis_tac[]);

val MergeL_empty = prove(
  ``MergeL (l1 ++ [emptyG] ++ l2) = MergeL (l1 ++ l2)``,
  Induct_on `l1` >> simp[]);

val MergeL_append = prove(
  ``MergeL (l1 ++ l2) = merge_graph (MergeL l1) (MergeL l2)``,
  Induct_on `l1` >> simp[merge_graph_ASSOC])

(*
val graphOf_correct_lemma = store_thm(
  "graphOf_correct_lemma",
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      ∀i0 i0' m0' g0.
        i0 ≠ [] ∧ graphOf i0 m0 c0 = SOME (i0', m0', g0) ⇒
        ∃i' g.
          graphOf i0 m c = SOME(i', m0', g) ∧
          ∀g'. gtouches g g' ⇒ gtouches g0 g'``,
  ho_match_mp_tac eval_ind' >> rpt conj_tac
  >- ((* seq head takes one step *)
      ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      rpt strip_tac >>
      qmatch_assum_rename_tac `graphOf i0 m0 c0 = SOME(i00,m00,g00)` [] >>
      `∃i' g'. graphOf i0 m c = SOME(i',m00,g') ∧
               ∀g''. gtouches g' g'' ⇒ gtouches g00 g''`
         by metis_tac[] >> simp[] >>
      qmatch_assum_rename_tac `
        graphOf i00 m00 (Seq rest) = SOME(i0',m0',rg)` []>>
      `i00 ≠ [] ∧ i' ≠ []` by metis_tac[graphOf_iterations_apart, LENGTH_NIL] >>
      `∃f. graphOf i' m00 (Seq rest) = SOME(f i0',m0',imap f rg) ∧
           i' = f i00 ∧ INJ f (i0' INSERT iterations rg) UNIV`
        by metis_tac[graphOf_starting_id_irrelevant] >>
      simp[] >> fs[INJ_INSERT, IN_imap] >> dsimp[] >>
      dsimp[gtouches_def] >> rpt strip_tac
      >- (fs[gtouches_def] >> metis_tac[]) >>
      disj2_tac >>
      `(∀j. j ∈ iterations rg ⇒ i00 ≤ j) ∧ ∀j. j ∈ iterations g00 ⇒ j < i00`
        by metis_tac[graphOf_iterations_apart] >>
      `∀a. a ∈ rg ⇒ a.iter ∉ iterations g00` suffices_by metis_tac[] >>
      qx_gen_tac `a` >> strip_tac >>
      `a.iter ∈ iterations rg` by simp[iterations_thm] >>
      metis_tac[ilistLTE_trans, ilistLE_REFL])
  >- ((* seq head is Done *)
      simp[Once graphOf_def, SimpL ``$==>``] >>
      simp[EXISTS_PROD])
  >- ((* seq of empty list moves to Done *)
      simp[graphOf_def])
  >- ((* guard of if evaluates to boolean and next statement selected *)
      map_every qx_gen_tac [`m0`, `gd`, `t`, `e`, `b`] >>
      rpt gen_tac >> strip_tac >> simp[Once graphOf_def, SimpL ``$==>``] >>
      Cases_on `b` >> simp[EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      map_every qx_gen_tac [`i0`, `i`, `m`, `g`] >>
      strip_tac >>
      qmatch_assum_rename_tac `graphOf (stackInc i0) m0 cc = SOME (i,m,g)` []>>
      `∃f. graphOf i0 m0 cc = SOME (f i, m, imap f g) ∧
           INJ f (i INSERT iterations g) UNIV ∧
           i0 = f (stackInc i0)`
        by metis_tac[graphOf_starting_id_irrelevant, stackInc_EQ_NIL] >>
      simp[])
  >- ((* guard of if evaluates to non-boolean (type error) *)
      rpt gen_tac >> strip_tac >> simp[graphOf_def] >>
      Cases_on `evalexpr m0 g` >> simp[] >> fs[])
  >- ((* assignment to var completes *)
      simp[graphOf_def, PULL_EXISTS, evalexpr_def, OPT_SEQUENCE_EQ_SOME,
           MEM_MAP, isDValue_destDValue, updf_def])
  >- ((* assignment to var fails *)
      simp[graphOf_def, PULL_EXISTS, updf_def])
  >- ((* assignment to array completes *)
      simp[graphOf_def, PULL_EXISTS, evalexpr_def, OPT_SEQUENCE_EQ_SOME,
           MEM_MAP, isDValue_destDValue])
  >- ((* assignment to array fails at upd_array stage *)
      simp[graphOf_def, PULL_EXISTS, evalexpr_def, OPT_SEQUENCE_EQ_SOME,
           isDValue_destDValue])
  >- ((* index of array assignment is evaluated *)
      simp[graphOf_def, PULL_EXISTS, evalexpr_def, readAction_def,
           expr_reads_def] >> rpt strip_tac >- fs[touches_def] >>
      metis_tac[])
  >- ((* array-read inside array assignment has index evaluated *)
      map_every qx_gen_tac [`pfx`, `ray`, `ri_e`, `sfx`, `way`, `wi_e`,
                            `vf`, `m0`] >> strip_tac >>
      simp[graphOf_def, PULL_EXISTS, evalDexpr_def, evalexpr_def,
           OPT_SEQUENCE_EQ_SOME, MEM_MAP, getReads_APPEND,
           getReads_def] >>
      map_every qx_gen_tac [`it`, `m0'`, `wi`, `sr`, `pr`, `ri`] >>
      simp[MAP_MAP_o, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      csimp[] >> rpt strip_tac
      >- metis_tac[]
      >- (fs[dvreadAction_def, touches_def, dvread_def,
             expr_reads_def] >> metis_tac[])
      >- (fs[touches_def] >> metis_tac[]))
  >- ((* array-read inside array assignment actually reads memory *)
      dsimp[graphOf_def, OPT_SEQUENCE_EQ_SOME, MEM_MAP, evalDexpr_def,
            evalexpr_def] >>
      dsimp[getReads_APPEND, getReads_def] >>
      simp[touches_def, dvreadAction_def, dvread_def] >>
      metis_tac[])
  >- ((* var-read inside array assignment reads memory *)
      dsimp[graphOf_def, OPT_SEQUENCE_EQ_SOME, evalDexpr_def, MEM_MAP] >>
      dsimp[getReads_def, getReads_APPEND] >>
      simp[touches_def, dvreadAction_def, dvread_def] >> metis_tac[])
  >- ((* forloop turns into seq *)
      rpt gen_tac >> strip_tac >> simp[Once graphOf_def, SimpL ``$==>``] >>
      simp[EXISTS_PROD, PULL_EXISTS] >>
      metis_tac[stackInc_EQ_NIL, graphOf_starting_id_irrelevant,
                gtouches_imap])
  >- ((* forloop aborts because domain evaluates badly *)
      ONCE_REWRITE_TAC [graphOf_def] >> simp[])
  >- ((* parloop turns into par *)
      rpt gen_tac >> strip_tac >> simp[Once graphOf_def, SimpL ``$==>``] >>
      simp[EXISTS_PROD, PULL_EXISTS] >>
      metis_tac[stackInc_EQ_NIL, graphOf_starting_id_irrelevant,
                gtouches_imap])
  >- ((* parloop aborts because domain evaluates badly *)
      ONCE_REWRITE_TAC [graphOf_def] >> simp[])
  >- ((* one component of a par takes a step *)
      map_every qx_gen_tac [`m0`, `m`, `pfx`, `c0`, `c`, `sfx`] >>
      strip_tac >> ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, OPT_SEQUENCE_EQ_SOME, MEM_MAP, MEM_MAPi,
           combinTheory.o_ABS_R] >>
      qabbrev_tac `
        TOS = λt:(num list # memory #
                  (value, actionRW, num list)action_graph) option.
               THE (OPTION_MAP (SND o SND) t)` >> simp[] >>
      map_every qx_gen_tac [`i0`, `m00`] >>
      qabbrev_tac `GG = λn. graphOf (i0 ++ [n;0])` >> simp[] >>
      strip_tac >>
      first_x_assum (qx_choosel_then [`gi`, `gm`, `gg`] assume_tac o
                     SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM,
                                           EXISTS_PROD,
                                           SKOLEM_THM]) >>
      qabbrev_tac `ci = LENGTH pfx` >>
      `GG ci m0 c0 = SOME(gi ci,gm ci,gg ci)`
        by (first_x_assum (qspec_then `ci` mp_tac) >>
            simp[Abbr`ci`, EL_APPEND1, EL_APPEND2]) >>
      first_x_assum (qspec_then `i0 ++ [ci;0]` mp_tac) >> simp[] >>
      disch_then (qx_choosel_then [`ci'`, `cg'`] strip_assume_tac) >>
      `pcg_eval (gg ci) (SOME m0) = SOME (gm ci)`
        by (simp[Abbr`GG`] >> fs[] >>
            metis_tac[graphOf_pcg_eval, APPEND_eq_NIL]) >>
      `∀a b c. TOS (SOME (a,b,c)) = c` by simp[Abbr`TOS`] >>
      lfs[] >>
      `∀n. n < ci + (LENGTH sfx + 1) ∧ n ≠ ci ⇒
           ∃m'. GG n m (EL n (pfx ++ [c] ++ sfx)) = SOME (gi n, m', gg n)`
        by (gen_tac >> strip_tac >>
            Cases_on `n < ci`
            >- (simp[EL_APPEND1] >>
                Cases_on `m = m0` >> simp[]
                >- (first_x_assum (qspec_then `n` mp_tac) >>
                    simp[EL_APPEND1]) >>
                `∃a. a ∈ gg ci ∧ (∀b. b ∈ pregraph a (gg ci) ⇒ b.write = NONE) ∧
                     apply_action a (SOME m0) = SOME m`
                  by metis_tac[eval_graphOf_action, APPEND_eq_NIL] >>
                first_x_assum (qspec_then `n` mp_tac) >> simp[EL_APPEND1] >>
                strip_tac >>
                `∀b. b ∈ gg n ⇒ a ≁ₜ b`
                  by (first_x_assum (qspecl_then [`n`, `ci`] mp_tac) >>
                      simp[gtouches_def] >> metis_tac[touches_SYM]) >>
                simp[Abbr`GG`] >> fs[] >>
                metis_tac[graphOf_apply_action_diamond, APPEND_eq_NIL]) >>
            `ci < n ∧ n < ci + (LENGTH sfx + 1)` by decide_tac >>
            simp[EL_APPEND1, EL_APPEND2] >>
            Cases_on `m = m0` >> simp[]
            >- (first_x_assum (qspec_then `n` mp_tac) >>
                simp[EL_APPEND1, EL_APPEND2]) >>
            `∃a. a ∈ gg ci ∧ (∀b. b ∈ pregraph a (gg ci) ⇒ b.write = NONE) ∧
                 apply_action a (SOME m0) = SOME m`
              by metis_tac[eval_graphOf_action, APPEND_eq_NIL] >>
            first_x_assum (qspec_then `n` mp_tac) >>
            simp[EL_APPEND1, EL_APPEND2] >> strip_tac >>
            `∀b. b ∈ gg n ⇒ a ≁ₜ b`
              by (first_x_assum (qspecl_then [`ci`, `n`] mp_tac) >>
                  simp[gtouches_def] >> metis_tac[touches_SYM]) >>
            simp[Abbr`GG`] >> fs[] >>
            metis_tac[graphOf_apply_action_diamond, APPEND_eq_NIL]) >>
      conj_tac
      >- (qx_gen_tac `n` >> strip_tac >> reverse (Cases_on `n = ci`)
          >- metis_tac[] >> simp[EL_APPEND2, EL_APPEND1]) >>
      pop_assum (qx_choose_then `gm'` assume_tac o
                 SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])>>
      `∀i j. i < j ∧ j < ci + (LENGTH sfx + 1) ⇒
             ¬gtouches (TOS (GG i m (EL i (pfx ++ [c] ++ sfx))))
                       (TOS (GG j m (EL j (pfx ++ [c] ++ sfx))))`
        by (rpt gen_tac >> strip_tac >>
            Cases_on `i = ci` >> simp[]
            >- (simp[EL_APPEND1, EL_APPEND2] >> metis_tac[]) >>
            Cases_on `j = ci` >> simp[] >>
            simp[EL_APPEND1, EL_APPEND2] >> metis_tac[gtouches_SYM]) >>
      conj_tac >- metis_tac[] >>
      `pcg_eval cg' (SOME m) = SOME (gm ci)`
        by (simp[Abbr`GG`] >> fs[] >>
            metis_tac[graphOf_pcg_eval, APPEND_eq_NIL]) >>
      fs[MAPi_APPEND, combinTheory.o_ABS_L] >>
      `∀n. n < ci ⇒ TOS (GG n m (EL n pfx)) = gg n ∧
                     TOS (GG n m0 (EL n pfx)) = gg n`
        by (rpt strip_tac
            >- (Q.SUBGOAL_THEN `n < ci + (LENGTH sfx + 1) ∧ n ≠ ci`
                 (fn th => first_x_assum (mp_tac o C MATCH_MP th))
                >- decide_tac >> simp[EL_APPEND1]) >>
            `n < ci + (LENGTH sfx + 1)` by decide_tac >>
            pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
            simp[EL_APPEND1]) >>
      `∀n. n < LENGTH sfx ⇒
           TOS (GG (ci + (n + 1)) m0 (EL n sfx)) = gg (ci + (n + 1)) ∧
           TOS (GG (ci + (n + 1)) m (EL n sfx)) = gg (ci + (n + 1))`
        by (rpt strip_tac
            >- (`ci + (n + 1) < ci + (LENGTH sfx + 1)` by decide_tac >>
                pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
                simp[EL_APPEND2]) >>
            Q.SUBGOAL_THEN
              `ci + (n + 1) < ci + (LENGTH sfx + 1) ∧ ci + (n + 1) ≠ ci`
              (fn th => first_x_assum (mp_tac o C MATCH_MP th))
            >- decide_tac >>
            simp[EL_APPEND2]) >>
      lfs[MAPi_GENLIST, Cong GENLIST_CONG] >>
      full_simp_tac (srw_ss() ++ ETA_ss) [] >>
      `∀g. MEM g (GENLIST gg ci) ⇒
           ¬gtouches g cg' ∧ ¬gtouches g (gg ci) ∧
           DISJOINT (iterations g) (iterations cg') ∧
           DISJOINT (iterations g) (iterations (gg ci))`
        by (simp[MEM_GENLIST, PULL_EXISTS] >> qx_gen_tac `n` >>
            strip_tac >> conj_tac
            >- (first_x_assum (qspecl_then [`n`, `ci`] mp_tac) >>
                simp[EL_APPEND2, EL_APPEND1] >>
                first_x_assum (qspec_then `n` mp_tac) >>
                simp[EL_APPEND2, EL_APPEND1]) >>
            `n < ci + (LENGTH sfx + 1)` by decide_tac >>
            pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
            simp[EL_APPEND1] >> qunabbrev_tac `GG` >> fs[] >> strip_tac >>
            `(∀it. it ∈ iterations (gg n) ⇒
                   TAKE (LENGTH (i0 ++ [n;0]) - 1) it =
                   FRONT (i0 ++ [n;0])) ∧
             (∀it. it ∈ iterations cg' ∨ it ∈ iterations (gg ci) ⇒
                   TAKE (LENGTH (i0 ++ [ci;0]) - 1) it =
                   FRONT (i0 ++ [ci;0]))`
              by metis_tac[graphOf_iterations_apart, APPEND_eq_NIL] >>
            fs[FRONT_APPEND] >> simp[DISJOINT_DEF, EXTENSION] >>
            `i0 ++ [ci] ≠ i0 ++ [n]` by simp[] >>
            metis_tac[]) >>
      fs[FOLDR_merge_lemma] >>
      conj_tac
      >- (qmatch_abbrev_tac `
            pcg_eval (merge_graph cg' RestG) (SOME m) = SOME m00
          ` >>
          `DISJOINT (iterations cg') (iterations RestG) ∧
           DISJOINT (iterations (gg ci)) (iterations RestG)`
            suffices_by (strip_tac >> fs[pcg_eval_merge_graph']) >>
          ONCE_REWRITE_TAC [DISJOINT_SYM] >>
          simp[Abbr`RestG`, iterations_MergeL, PULL_EXISTS] >>
          simp[MEM_GENLIST, PULL_EXISTS, PULL_FORALL] >>
          `∀n. n < LENGTH sfx ⇒
               DISJOINT (iterations (gg (ci + (n + 1))))
                        (iterations cg') ∧
               DISJOINT (iterations (gg (ci + (n + 1))))
                        (iterations (gg ci))`
            suffices_by metis_tac[] >>
          gen_tac >> strip_tac >>
          `ci + (n + 1) < ci + (LENGTH sfx + 1)` by decide_tac >>
          pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
          simp[EL_APPEND2] >> qunabbrev_tac `GG` >> fs[] >> strip_tac >>
          `(∀it. it ∈ iterations (gg (ci + (n + 1))) ⇒
                 TAKE (LENGTH (i0 ++ [ci + (n + 1);0]) - 1) it =
                 FRONT (i0 ++ [ci + (n + 1);0])) ∧
           (∀it. it ∈ iterations cg' ∨ it ∈ iterations (gg ci) ⇒
                 TAKE (LENGTH (i0 ++ [ci;0]) - 1) it =
                 FRONT (i0 ++ [ci;0]))`
            by metis_tac[graphOf_iterations_apart, APPEND_eq_NIL] >>
          fs[FRONT_APPEND] >>
          `i0 ++ [ci] ≠ i0 ++ [ci + (n + 1)]` by simp[] >>
          simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      qmatch_abbrev_tac `
        ∀g'. gtouches (merge_graph cg' BG) g' ⇒
             gtouches (merge_graph (gg ci) BG) g'` >>
      simp[gtouches_def, IN_merge_graph, PULL_EXISTS] >>
      map_every qx_gen_tac [`g'`, `a1`, `a2`] >> strip_tac
      >- metis_tac[gtouches_def] >>
      map_every qexists_tac [`a1`, `a2`] >> simp[] >>
      `a1.iter ∉ iterations (gg ci)` suffices_by simp[] >>
      strip_tac >>
      `a1.iter ∈ iterations BG` by simp[iterations_thm] >>
      fs[iterations_FOLDR_merge_graph, Abbr`BG`]
      >- (res_tac >> fs[DISJOINT_DEF, EXTENSION] >>
          metis_tac[]) >>
      qpat_assum `MEM g (GENLIST f n)` mp_tac >>
      simp[MEM_GENLIST, PULL_EXISTS] >> qx_gen_tac `n` >>
      disjneq_search >> BasicProvers.VAR_EQ_TAC >> strip_tac >>
      `ci + (n + 1) < ci + (LENGTH sfx + 1)` by decide_tac >>
      pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
      simp[EL_APPEND2, Abbr`GG`] >> strip_tac >> fs[] >>
      `TAKE (LENGTH (i0 ++ [ci; 0]) - 1) a1.iter =
       FRONT (i0 ++ [ci;0]) ∧
       TAKE (LENGTH (i0 ++ [ci + (n + 1); 0]) - 1) a1.iter =
       FRONT (i0 ++ [ci + (n + 1);0])`
        by metis_tac[graphOf_iterations_apart, APPEND_eq_NIL] >>
      fs[FRONT_APPEND])
  >- ((* par has a Done component *)
      ONCE_REWRITE_TAC [graphOf_def] >>
      simp[OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R, MEM_MAP,
           MEM_MAPi, PULL_EXISTS, MergeL_empty, combinTheory.o_ABS_L] >>
      qabbrev_tac `
        TOS = λt:(num list # memory #
                  (value, actionRW, num list)action_graph) option.
               THE (OPTION_MAP (SND o SND) t)` >>
      simp[] >>
      map_every qx_gen_tac [`m0`, `pfx`, `sfx`, `i0`, `m0'`] >>
      qabbrev_tac `GG = λn. graphOf (i0 ++ [n;0])` >> simp[] >>
      strip_tac >>
      first_x_assum (qx_choosel_then [`gi`, `gm`, `gg`] assume_tac o
                     SIMP_RULE (srw_ss()) [EXISTS_PROD, SKOLEM_THM,
                                           GSYM RIGHT_EXISTS_IMP_THM]) >>
      `∀n. n < LENGTH pfx ⇒ GG n m0 (EL n pfx) = SOME(gi n, gm n, gg n)`
        by (rpt strip_tac >> first_x_assum (qspec_then `n` mp_tac) >>
            simp[EL_APPEND1]) >>
      qabbrev_tac `p = LENGTH pfx` >>
      `∀n. n < LENGTH sfx ⇒
           ∃f. GG (n + p) m0 (EL n sfx) =
               SOME (f (gi (n + (p + 1))),
                     gm (n + (p + 1)),
                     imap f (gg (n + (p + 1))))`
        by (rpt strip_tac >>
            `n + (p + 1) < p + (LENGTH sfx + 1)` by decide_tac >>
            pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
            simp[Abbr`GG`, EL_APPEND2] >>
            `i0 ++ [n + (p + 1); 0] ≠ []` by simp[] >>
            disch_then (fn c1 => pop_assum (fn c2 =>
              mp_tac (MATCH_MP graphOf_starting_id_irrelevant
                               (CONJ c1 c2)))) >>
            disch_then (qspec_then `i0 ++ [n + p; 0]` mp_tac) >> simp[] >>
            metis_tac[]) >>
      pop_assum (qx_choose_then `ff` assume_tac o
                 SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM])>>
      `∀a b c. TOS (SOME (a,b,c)) = c` by simp[Abbr`TOS`] >>
      rpt conj_tac
      >- (qx_gen_tac `n` >> strip_tac >>
          Cases_on `n < p` >> simp[EL_APPEND1, EL_APPEND2] >>
          first_x_assum (qspec_then `n - p` mp_tac) >> simp[])
      >- (map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
          Cases_on `j < p`
          >- (first_x_assum (qspecl_then [`i`, `j`] mp_tac) >>
              simp[EL_APPEND1]) >>
          `0 < LENGTH sfx` by decide_tac >>
          simp[EL_APPEND2] >>
          first_assum (qspec_then `j - p` mp_tac) >>
          simp_tac (srw_ss() ++ ARITH_ss) [ASSUME ``¬(j:num < p)``] >>
          simp[] >> strip_tac >> lfs[] >>
          Cases_on `i < p` >- simp[EL_APPEND1] >>
          first_x_assum (qspec_then `i - p` mp_tac) >> simp[EL_APPEND2])
      >- (simp[MAPi_APPEND] >>
          simp[MAPi_GENLIST, combinTheory.S_ABS_L, combinTheory.o_ABS_L] >>
          simp[Cong GENLIST_CONG] >>
          fs[MAPi_APPEND] >>
          `∀i m. GG i m Done = SOME(i0 ++ [i;0], m, emptyG)`
            by simp[Abbr`GG`, graphOf_def] >>
          fs[MergeL_empty] >>
          fs[MAPi_GENLIST, combinTheory.o_ABS_L, combinTheory.S_ABS_L] >>
          lfs[Cong GENLIST_CONG] >>
          `GENLIST (λn. TOS (GG (n + (p + 1)) m0 (EL n sfx))) (LENGTH sfx) =
           GENLIST (λn. gg (n + (p + 1))) (LENGTH sfx)`
            by (simp[LIST_EQ_REWRITE] >> qx_gen_tac `m` >> strip_tac >>
                `p + (m + 1) < p + (LENGTH sfx + 1)` by simp[] >>
                pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
                simp[EL_APPEND2]) >>
          fs[] >> fs[MergeL_append] >> full_simp_tac (srw_ss() ++ ETA_ss) [] >>
          qmatch_abbrev_tac `
            pcg_eval (merge_graph (MergeL (GENLIST gg p)) BG1) (SOME m0) =
            SOME m0'` >>
          `DISJOINT (iterations (MergeL (GENLIST gg p))) (iterations BG1)`
            by simp[Abbr`BG1`, iterations_MergeL, PULL_EXISTS, MEM_GENLIST]

          pcg_eval_merge_graph'














``
*)



val _ = export_theory();
