open HolKernel Parse boolLib bossLib;

open lcsymtacs

open bagTheory
open PseudoCTheory
open actionTheory
open pred_setTheory finite_mapTheory
open intLib
open optionTheory pairTheory listTheory rich_listTheory
open boolSimps
open indexedListsTheory
open relationTheory

val _ = new_theory "PseudoCProps";

val _ = set_trace "Goalstack.print_goal_at_top" 0

val veq = rpt BasicProvers.VAR_EQ_TAC

val bool_case_eq = prove_case_eq_thm{
  case_def= TypeBase.case_def_of ``:bool``,
  nchotomy = TypeBase.nchotomy_of ``:bool``
};

val option_case_eq = prove_case_eq_thm{
  case_def= option_case_def,
  nchotomy = option_CASES
               |> ONCE_REWRITE_RULE [DISJ_COMM]
};

val expr_case_eq = prove_case_eq_thm{
  case_def= TypeBase.case_def_of ``:expr``,
  nchotomy = TypeBase.nchotomy_of ``:expr``
};

val value_case_eq = prove_case_eq_thm{
  case_def= TypeBase.case_def_of ``:value``,
  nchotomy = TypeBase.nchotomy_of ``:value``
};

val pair_case_eq = prove_case_eq_thm{
  case_def= TypeBase.case_def_of ``:'a # 'b``
            |> INST_TYPE [alpha |-> gamma, beta |-> alpha, gamma |-> beta]
            |> GENL [``x:'a``, ``y:'b``, ``f:'a -> 'b -> 'c``] ,
  nchotomy = TypeBase.nchotomy_of ``:'a # 'b``
};

val expr_weight_def = Define`
  (expr_weight (Value v) = 0:num) ∧
  (expr_weight e = 1)
`;
val _ = export_rewrites ["expr_weight_def"]

val stmt_weight_def = tDefine "stmt_weight" `
  (stmt_weight Abort = 0) ∧
  (stmt_weight Done = 0) ∧
  (stmt_weight (Assign w ds v) =
     1 + ew (MAccess w) +
     SUM (MAP (λd. case d of DMA m => ew (MAccess m)
                           | DValue v => ew (Value v))
              ds)) ∧
  (stmt_weight (Malloc v d value) = 1) ∧
  (stmt_weight (IfStmt g t e) = MAX (stmt_weight t) (stmt_weight e) + 3) ∧
  (stmt_weight (ForLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (ParLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (While g b) = stmt_weight b + 1) ∧
  (stmt_weight (WaitUntil g) = 1) ∧
  (stmt_weight (Seq stmts) = SUM (MAP stmt_weight stmts) + LENGTH stmts) ∧
  (stmt_weight (Par stmts) =
    SUM (MAP stmt_weight stmts) + LENGTH stmts) ∧
  (stmt_weight (Label v s) = stmt_weight s + 1) ∧
  (stmt_weight (Local v e s) = stmt_weight s + 1) ∧
  (stmt_weight (Atomic s) = stmt_weight s + 1)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["stmt_weight_def"]

val seq_count_def = tDefine "seq_count" `
  (seq_count (Seq cs) = SUM (MAP seq_count cs) + 1) ∧
  (seq_count (Par cs) = SUM (MAP seq_count cs) + 1) ∧
  (seq_count (ParLoop v d s) = seq_count s) ∧
  (seq_count (ForLoop v d s) = seq_count s) ∧
  (seq_count (While g b) = seq_count b) ∧
  (seq_count (IfStmt g t e) = seq_count t + seq_count e) ∧
  (seq_count (Label v s) = seq_count s) ∧
  (seq_count (Local v e s) = seq_count s) ∧
  (seq_count (Atomic s) = seq_count s) ∧
  (seq_count _ = 0)
`
  (WF_REL_TAC `measure stmt_size` >> simp[] >> Induct >> simp[] >>
   rpt strip_tac >> simp[stmt_size_def] >> res_tac >> simp[])
val _ = export_rewrites ["seq_count_def"]

val loopbag_def = tDefine "loopbag" `
  (loopbag Abort = {| |}) ∧
  (loopbag Done = {| |}) ∧
  (loopbag (Label v s) = loopbag s) ∧
  (loopbag (Local v e s) = loopbag s) ∧
  (loopbag (Atomic s) = loopbag s) ∧
  (loopbag (Assign w ds v) = {| |}) ∧
  (loopbag (Malloc v d value) = {| |}) ∧
  (loopbag (IfStmt g t e) = BAG_UNION (loopbag t) (loopbag e)) ∧
  (loopbag (ForLoop v d s) = if loopbag s = {||} then {|1|}
                             else BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (ParLoop v d s) = if loopbag s = {||} then {|1|}
                             else BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (While g b) = loopbag b) ∧
  (loopbag (WaitUntil g) = {||}) ∧
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
      (λ(m:memory,s). (loopbag s, stmt_weight expr_weight s, seq_count s))``
)

val WF_evalR = store_thm(
  "WF_evalR",
  ``WF evalR``,
  simp[WF_LEX, WF_TC_EQN, WF_inv_image, bagTheory.WF_mlt1]);

val WF_eval_induction =
    WF_INDUCTION_THM
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
  >- (match_mp_tac TC_SUBSET >> simp[mlt1_def]) >>
  `mlt R b (BAG_INSERT e b)`
    by (match_mp_tac TC_SUBSET >>
        simp[mlt1_def] >> map_every qexists_tac [`e`, `{||}`, `b`] >>
        simp[] >> simp[BAG_EXTENSION, BAG_INN, BAG_INSERT, BAG_UNION,
                       EMPTY_BAG] >>
        map_every qx_gen_tac [`m`, `d`] >> Cases_on `d = e` >> simp[]) >>
  metis_tac[TC_RULES]);

val FOLDR_KI = store_thm(
  "FOLDR_KI[simp]",
  ``FOLDR (\e a. a) acc list = acc``,
  Induct_on `list` >> simp[]);

val SND_ap2 = store_thm(
  "SND_ap2[simp]",
  ``SND (ap2 f p) = f (SND p)``,
  Cases_on `p` >> simp[]);

val expr_weight_esubst = store_thm(
  "expr_weight_esubst",
  ``∀e. expr_weight (esubst vnm value e) ≤ expr_weight e``,
  Induct >> simp[esubst_def] >> rw[] >>
  Cases_on `m` >> simp[esubst_def] >> rw[]);

val stmt_weight_ssubst = store_thm(
  "stmt_weight_ssubst",
  ``∀s vnm value.
      stmt_weight expr_weight (ssubst vnm value s) ≤
      stmt_weight expr_weight s``,
  ho_match_mp_tac stmt_induction >> simp[ssubst_def, MAP_MAP_o] >> rw[]
  >- (simp[combinTheory.o_DEF] >>
      Induct_on `ds` >> simp[] >> qx_gen_tac `h` >>
      match_mp_tac arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
      simp[] >> Cases_on `h` >> simp[] >> Cases_on `m` >> rw[])
  >- (Cases_on `d` >> simp[ssubst_def] >> rw[])
  >- (Cases_on `d` >> simp[ssubst_def] >> rw[])
  >- (simp[combinTheory.o_ABS_R] >> Induct_on `stmts` >> dsimp[] >>
      rpt strip_tac >>
      match_mp_tac arithmeticTheory.LESS_EQ_LESS_EQ_MONO >> simp[])
  >- (simp[combinTheory.o_ABS_R] >> Induct_on `stmts` >> dsimp[] >>
      rpt strip_tac >>
      match_mp_tac arithmeticTheory.LESS_EQ_LESS_EQ_MONO >> simp[])
  >- (rw[]))

val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ whilefree (SND a) ⇒ evalR b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[LEX_DEF, MAX_SET_THM, SUM_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
  >- (Induct_on `pfx` >> simp[])
  >- (Induct_on `pfx` >> simp[])
  >- (Induct_on `pfx` >> simp[])
  >- (metis_tac[])
  >- (metis_tac[])
  >- (Cases_on `b` >> simp[MAX_PLUS])
  >- (metis_tac[])
  >- (rw[] >> simp[FOLDR_MAP, mlt_loopbag_lemma])
  >- (rw[])
  >- (rw[] >> simp[FOLDR_MAP, mlt_loopbag_lemma])
  >- (rw[])
  >- (rw[] >> fs[DISJ_IMP_THM, FORALL_AND_THM]
      >- (disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
          Induct_on `sfx` >> simp[])
      >- (disj2_tac >> rw[] >> Induct_on `pfx` >> simp[])
      >- (disj2_tac >> rw[] >> Induct_on `pfx` >> simp[]))
  >- (metis_tac[])
  >- (metis_tac[])
  >- (metis_tac[])
  >- (simp[DECIDE ``x < y + 1n ⇔ x ≤ y``, stmt_weight_ssubst])
);

val strip_label_def = tDefine "strip_label" `
  (strip_label (IfStmt gd t e) = IfStmt gd (strip_label t) (strip_label e)) ∧
  (strip_label (ForLoop v dom s) = ForLoop v dom (strip_label s)) ∧
  (strip_label (ParLoop v dom s) = ParLoop v dom (strip_label s)) ∧
  (strip_label (Seq stmts) = Seq (MAP strip_label stmts)) ∧
  (strip_label (Par stmts) = Par (MAP strip_label stmts)) ∧
  (strip_label (Label v s) = strip_label s) ∧
  (strip_label (Local v e s) = Local v e (strip_label s)) ∧
  (strip_label (Atomic s) = Atomic (strip_label s)) ∧
  (strip_label (While g b) = While g (strip_label b)) ∧
  (strip_label s = s)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >> rpt strip_tac >> res_tac >>
   simp[]);
val _ = export_rewrites ["strip_label_def"]

val strip_label_idem = store_thm(
  "strip_label_idem[simp]",
  ``(!s. strip_label (strip_label s) = strip_label s) ∧
    (strip_label o strip_label = strip_label)``,
  simp[FUN_EQ_THM] >> ho_match_mp_tac stmt_induction >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]);

val eval_ind' = save_thm(
  "eval_ind'",
  PseudoCTheory.eval_strongind
    |> SIMP_RULE (srw_ss()) [FORALL_PROD]
    |> Q.SPEC `\a1 a2. P (FST a1) (SND a1) (FST a2) (SND a2)`
    |> SIMP_RULE (srw_ss()) []);

val evaltc_seq = store_thm(
  "evaltc_seq",
  ``EVERY ($= Done) pfx ∧ (m0,c0) --->⁺ (m,c) ⇒
    (m0, Seq (pfx ++ [c0] ++ sfx)) --->⁺ (m, Seq (pfx ++ [c] ++ sfx))``,
  Cases_on `EVERY ($= Done) pfx` >> simp[] >>
  `(∃x0. (m0,c0) = x0) ∧ (∃x. (m,c) = x)` by simp[] >> simp[] >>
  disch_then (fn th => ntac 2 (pop_assum mp_tac) >>
                       map_every qid_spec_tac [`m0`, `m`, `c0`, `c`] >>
                       mp_tac th) >>
  map_every qid_spec_tac [`x`, `x0`] >>
  Induct_on `TC` >> rw[] >- metis_tac[TC_SUBSET, eval_rules] >>
  qmatch_assum_rename_tac `(m0,c0) --->⁺ y` >> Cases_on `y` >> fs[] >>
  metis_tac[TC_RULES]);

val evalrtc_seqpar = prove(
  ``(m0,c0) --->* (m,c) ⇒
    (ct = Seq ∧ EVERY ($= Done) pfx ∨ ct = Par) ⇒
    (m0, ct (pfx ++ [c0] ++ sfx)) --->* (m, ct (pfx ++ [c] ++ sfx))``,
  Cases_on `EVERY ($= Done) pfx` >> simp[] >>
  `(∃x0. (m0,c0) = x0) ∧ (∃x. (m,c) = x)` by simp[] >> simp[] >>
  disch_then (fn th => ntac 2 (pop_assum mp_tac) >>
                       map_every qid_spec_tac [`m0`, `m`, `c0`, `c`] >>
                       mp_tac th) >>
  map_every qid_spec_tac [`x`, `x0`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[FORALL_PROD] >>
  metis_tac[RTC_RULES, eval_rules]);

val (evalrtc_seq, evalrtc_par) =
    evalrtc_seqpar |> Q.GEN `ct`
                   |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM,
                                            AND_IMP_INTRO, LEFT_AND_OVER_OR]
                   |> CONJ_PAIR

val _ = save_thm("evalrtc_seq", evalrtc_seq)
val _ = save_thm("evalrtc_par", evalrtc_par)

val _ = augment_srw_ss [ETA_ss]

val _ = overload_on("labelled", ``λvs s. FOLDR Label s vs``)

val strip_label_labelled = store_thm(
  "strip_label_labelled[simp]",
  ``∀vs. strip_label (labelled vs s) = strip_label s``,
  Induct >> simp[]);

val s = mk_var("s", ``:stmt``)
val vs = mk_var("vs", ``:value list``)
val lvs_s = ``labelled vs s``
fun mklabelled11_eqn c = let
  val (argtys, _) = strip_fun (type_of c)
  val args0 = map (fn ty => mk_var("x", ty)) argtys
  val args = foldr (fn (a, acc) => variant acc a :: acc) [] args0
  val c_args = list_mk_comb(c, args)
  val eqn = mk_eq(c_args, lvs_s)
  val iff = mk_eq(eqn, mk_conj(``^vs = []``, mk_eq(s, c_args)))
in
  prove(iff, Cases_on `^vs` >> simp[EQ_SYM_EQ])
end

val label_EQ_labelled = prove(
  ``Label v s1 = labelled vs s2 ⇔
      (∃t. vs = v::t ∧ s1 = labelled t s2) ∨ vs = [] ∧ s2 = Label v s1``,
  Cases_on `vs` >> simp[EQ_SYM_EQ]);

val labelled_EQ = save_thm(
  "labelled_EQ[simp]",
  LIST_CONJ
    (label_EQ_labelled ::
     map mklabelled11_eqn
         (op_set_diff equal (TypeBase.constructors_of ``:stmt``) [``Label``])))

val strip_label_EQ_Abort = store_thm(
  "strip_label_EQ_Abort[simp]",
  ``∀c. strip_label c = Abort ⇔ ∃vs. c = labelled vs Abort``,
  ho_match_mp_tac stmt_induction >> simp[EQ_SYM_EQ]);

val strip_label_EQ_Assign = store_thm(
  "strip_label_EQ_Assign[simp]",
  ``∀c x y z.
      strip_label c = Assign x y z ⇔ ∃vs. c = labelled vs (Assign x y z)``,
  ho_match_mp_tac stmt_induction >> simp[EQ_SYM_EQ]);

val strip_label_EQ_ForLoop = store_thm(
  "strip_label_EQ_ForLoop[simp]",
  ``∀c vn d s.
      strip_label c = ForLoop vn d s ⇔
      ∃vs s'. c = labelled vs (ForLoop vn d s') ∧
              strip_label s' = s``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >>
  metis_tac[]);

val strip_label_EQ_Malloc = store_thm(
  "strip_label_EQ_Malloc[simp]",
  ``∀c anm sz i.
       strip_label c = Malloc anm sz i ⇔
       ∃vs. c = labelled vs (Malloc anm sz i)``,
  ho_match_mp_tac stmt_induction >> simp[EQ_SYM_EQ]);

val strip_label_EQ_Par = store_thm(
  "strip_label_EQ_Par[simp]",
  ``∀c stmts. strip_label c = Par stmts ⇔
              ∃vs sts'. c = labelled vs (Par sts') ∧
                        MAP strip_label sts' = stmts``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_EQ_ParLoop = store_thm(
  "strip_label_EQ_ParLoop[simp]",
  ``∀c vn d s.
      strip_label c = ParLoop vn d s ⇔
      ∃vs s'. c = labelled vs (ParLoop vn d s') ∧
              strip_label s' = s``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >>
  metis_tac[]);

val strip_label_EQ_Seq = store_thm(
  "strip_label_EQ_Seq[simp]",
  ``∀c stmts. strip_label c = Seq stmts ⇔
              ∃vs sts'. c = labelled vs (Seq sts') ∧
                        MAP strip_label sts' = stmts``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_EQ_Done = store_thm(
  "strip_label_EQ_Done[simp]",
  ``∀c. strip_label c = Done ⇔ ∃vs. c = labelled vs Done``,
  ho_match_mp_tac stmt_induction >> simp[]);

val strip_label_EQ_If = store_thm(
  "strip_label_EQ_If[simp]",
  ``∀c gd t e.
      strip_label c = IfStmt gd t e ⇔
      ∃vs t' e'.
        c = labelled vs (IfStmt gd t' e') ∧
        strip_label t' = t ∧
        strip_label e' = e``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_EQ_Local = store_thm(
  "strip_label_EQ_Local[simp]",
  ``∀c v e s. strip_label c = Local v e s ⇔
              ∃vs s'. c = labelled vs (Local v e s') ∧
                      strip_label s' = s``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_EQ_Atomic = store_thm(
  "strip_label_EQ_Atomic[simp]",
  ``∀c s. strip_label c = Atomic s ⇔
          ∃vs s'. c = labelled vs (Atomic s') ∧
                  strip_label s' = s``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_EQ_While = store_thm(
  "strip_label_EQ_While[simp]",
  ``∀c g b. strip_label c = While g b ⇔
            ∃vs b'. c = labelled vs (While g b') ∧
                    strip_label b' = b``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_EQ_WaitUntil = store_thm(
  "strip_label_EQ_WaitUntil[simp]",
  ``∀c g. strip_label c = WaitUntil g ⇔
          ∃vs. c = labelled vs (WaitUntil g)``,
  ho_match_mp_tac stmt_induction >> simp[PULL_EXISTS] >> metis_tac[]);

val strip_label_ssubst = store_thm(
  "strip_label_ssubst[simp]",
  ``∀s. strip_label (ssubst vnm v s) = ssubst vnm v (strip_label s)``,
  ho_match_mp_tac stmt_induction >>
  simp[ssubst_def, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FORALL_domain] >>
  rw[]);

val eval_rules' = CONJUNCTS (SIMP_RULE bool_ss [FORALL_BOOL, FORALL_AND_THM] eval_rules)

val e1tac =
    FIRST (List.mapPartial
             (fn th => case total MATCH_MP_TAC th of
                           NONE => SOME(MATCH_ACCEPT_TAC th)
                         | SOME t => SOME(t >> simp[] >> NO_TAC))
             eval_rules')
val etac =
    simp[] >> match_mp_tac RTC_SUBSET >> e1tac

val eval_Done = store_thm(
  "eval_Done[simp]",
  ``(m, Done) ---> x ⇔ F``,
  simp[Once eval_cases]);

val eval_Abort = store_thm(
  "eval_Abort[simp]",
  ``(m,Abort) ---> x ⇔ F``,
  simp[Once eval_cases]);

val evalrtc_Done = store_thm(
  "evalrtc_Done[simp]",
  ``(m, Done) --->* x ⇔ x = (m,Done)``,
  simp[Once RTC_CASES1, EQ_SYM_EQ]);

val evalrtc_Abort = store_thm(
  "evalrtc_Abort[simp]",
  ``(m, Abort) --->* x ⇔ x = (m, Abort)``,
  simp[Once RTC_CASES1, EQ_SYM_EQ]);

val MAP_EQ_CONS = prove(
  ``MAP f l1 = h::t ⇔ ∃h0 t0. l1 = h0::t0 ∧ t = MAP f t0 ∧ h = f h0``,
  Cases_on `l1` >> simp[EQ_SYM_EQ, CONJ_COMM]);

val MAP_EQ_APPEND = prove(
  ``∀l2 l1 l3. MAP f l1 = l2 ++ l3 ⇔
               ∃l2' l3'. l1 = l2' ++ l3' ∧ l2 = MAP f l2' ∧ l3 = MAP f l3'``,
  Induct >> simp[] >- simp[EQ_SYM_EQ] >> simp[MAP_EQ_CONS, PULL_EXISTS] >>
  metis_tac[]);

val labelled_eval_mono = store_thm(
  "labelled_eval_mono",
  ``∀m0 c0 m c. (m0,c0) ---> (m,c) ⇒
                (m0, labelled vs c0) ---> (m, labelled vs c)``,
  Induct_on `vs` >> simp[] >> metis_tac[eval_rules]);

val labelled_RTC_mono = save_thm(
  "labelled_RTC_mono",
  prove(``∀x0 x. x0 --->* x ⇒
                 ∀m0 m vs c0 c.
                   x0 = (m0,c0) ∧ x = (m,c) ⇒
                   (m0,labelled vs c0) --->* (m,labelled vs c)``,
        ho_match_mp_tac RTC_INDUCT >> simp[] >>
        simp[FORALL_PROD] >>
        metis_tac[labelled_eval_mono, RTC_RULES])
    |> SIMP_RULE (srw_ss()) [PULL_FORALL]);

val seqseq_mono_1Done = store_thm(
  "seqseq_mono_1Done[simp]",
  ``∀m0 c0 m c.
     (m0, Seq (Done::sts0)) ---> (m, res) ⇔
       (∃sts. res = Seq (Done::sts) ∧ (m0, Seq sts0) ---> (m, Seq sts)) ∨
       res = Abort ∧ m = m0 ∧ (m0, Seq sts0) ---> (m0, Abort) ∨
       res = Done ∧ m = m0 ∧ (m0, Seq sts0) ---> (m0, Done)``,
  simp [Once eval_cases, SimpLHS] >>
  rpt gen_tac >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [eval_cases])) >>
  simp[] >> Cases_on `res = Done` >> simp[] >>
  Cases_on `res = Abort` >> simp[] >>
  rw[EQ_IMP_THM]
  >- (fs[APPEND_EQ_CONS] >> rw[] >> fs[] >> metis_tac[])
  >- (dsimp[APPEND_EQ_CONS] >> metis_tac[])
  >- (fs[Once APPEND_EQ_CONS] >> dsimp[APPEND_EQ_CONS] >> rw[] >>
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [APPEND_EQ_CONS]) >>
      RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
      POP_ASSUM_LIST (map_every strip_assume_tac) >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >> metis_tac[]) >>
  map_every qexists_tac [`c`, `c0`, `Done::pfx`, `sfx`] >> simp[]);

val seq_mono_Dones = store_thm(
  "seq_mono_Dones[simp]",
  ``∀m0 c0 m c pfx sts0 res.
      EVERY ($= Done) pfx ⇒
      ((m0, Seq (pfx ++ sts0)) ---> (m, res) ⇔
         (∃sts. res = Seq (pfx ++ sts) ∧ (m0, Seq sts0) ---> (m, Seq sts)) ∨
         res = Done ∧ m = m0 ∧ (m0, Seq sts0) ---> (m, Done) ∨
         res = Abort ∧ m = m0 ∧ (m0, Seq sts0) ---> (m, Abort))``,
  Induct_on `pfx` >> simp[]
  >- (rpt gen_tac >> simp[SimpLHS, Once eval_cases] >> Cases_on `res = Done` >>
      simp[] >> simp[SimpRHS, Once eval_cases]
      >- metis_tac[] >>
      Cases_on `res = Abort` >> simp[PULL_EXISTS]
      >- (simp[Once eval_cases] >> metis_tac[]) >>
      metis_tac[]) >>
  metis_tac[]);

val rtc_mono1 = prove(
  ``!x0 x. x0 --->* x ⇒
           ∀m0 sts0 m sts pfx res.
              EVERY ($= Done) pfx ∧ x0 = (m0, Seq(pfx ++ sts0)) ∧
              x = (m, res) ⇒
                (∃sts. res = Seq(pfx ++ sts) ∧
                       (m0, Seq sts0) --->* (m, Seq sts)) ∨
                res = Done ∧ (m0, Seq sts0) --->* (m, Done) ∨
                res = Abort ∧ (m0, Seq sts0) --->* (m, Abort)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rw[] >>
  qpat_assum `(m0, Seq (pfx ++ sts0)) ---> x` mp_tac >>
  simp[Once eval_cases] >> reverse (rw[])
  >- (fs[] >> rw[] >>
      fs[APPEND_EQ_APPEND_MID, APPEND_EQ_CONS] >>
      rw[] >> fs[] >> etac)
  >- (fs[] >> etac) >>
  `c0 ≠ Done` by (strip_tac >> fs[]) >>
  first_x_assum
    ((fn th => fs[APPEND_EQ_APPEND_MID, APPEND_EQ_CONS] >>
               assume_tac th >>
               rpt BasicProvers.VAR_EQ_TAC) o
     assert(is_forall o concl)) >>
  fs[] >>
  pop_assum (qspecl_then [`l ++ [c] ++ sfx`, `pfx`] mp_tac) >>
  simp[] >> reverse strip_tac >> simp[] >>
  match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
  qexists_tac `(m', Seq (l ++ [c] ++ sfx))` >> simp[] >> e1tac)
  |> SIMP_RULE (srw_ss()) [PULL_FORALL]

val rtc_mono2a = prove(
  ``∀x0 x. x0 --->* x ⇒
           ∀m0 sts0 m sts pfx.
             EVERY ($= Done) pfx ∧ x0 = (m0, Seq sts0) ⇒
             x = (m, Seq sts) ⇒
             (m0, Seq(pfx ++ sts0)) --->* (m, Seq (pfx ++ sts))``,
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rw[] >>
  qpat_assum `(m0,Seq sts0) ---> y` mp_tac >>
  simp[Once eval_cases] >> reverse (rw[]) >- fs[] >- fs[] >>
  match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
  qexists_tac `(m',Seq (pfx ++ pfx' ++ [c] ++ sfx))` >>
  conj_tac >- (simp[] >> e1tac) >> metis_tac[]) |> SIMP_RULE (srw_ss()) [PULL_FORALL]

val rtc_mono2b = prove(
  ``∀x0 x.
       x0 --->* x ⇒
       ∀pfx sts m0 m.
         x0 = (m0, Seq sts) ∧ x = (m, Done) ∧ EVERY ($= Done) pfx ⇒
         (m0, Seq (pfx ++ sts)) --->* (m, Done)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rw[] >>
  simp[Once RTC_CASES1, EXISTS_PROD, PULL_EXISTS] >> dsimp[] >>
  qpat_assum `(m0, Seq sts) ---> x` mp_tac >>
  simp[Once eval_cases, SimpL ``$==>``] >> rw[]
  >- (disj1_tac >> map_every qexists_tac [`m'`, `pfx' ++ [c] ++ sfx`] >>
      conj_tac >- e1tac >> simp[]) >>
  disj2_tac >> fs[] >> e1tac) |> SIMP_RULE (srw_ss()) [PULL_FORALL]

val rtc_mono2c = prove(
  ``∀x0 x.
       x0 --->* x ⇒
       ∀pfx sts m0 m.
         x0 = (m0, Seq sts) ∧ x = (m, Abort) ∧ EVERY ($= Done) pfx ⇒
         (m0, Seq (pfx ++ sts)) --->* (m, Abort)``,
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rw[] >>
  simp[Once RTC_CASES1, EXISTS_PROD, PULL_EXISTS] >> dsimp[] >>
  qpat_assum `(m0, Seq sts) ---> x` mp_tac >>
  simp[Once eval_cases, SimpL ``$==>``] >> rw[]
  >- (disj1_tac >> map_every qexists_tac [`m'`, `pfx' ++ [c] ++ sfx`] >>
      conj_tac >- e1tac >> simp[]) >> fs[] >>
  disj2_tac >> e1tac);

val seqDones_rtc = store_thm(
  "seqDones_rtc[simp]",
  ``EVERY ($= Done) pfx ⇒
    ((m0, Seq (pfx ++ sts0)) --->* (m, res) ⇔
     (∃sts. res = Seq(pfx ++ sts) ∧ (m0, Seq sts0) --->* (m, Seq sts)) ∨
     res = Done ∧ (m0, Seq sts0) --->* (m, Done) ∨
     res = Abort ∧ (m0, Seq sts0) --->* (m, Abort))``,
  rw[EQ_IMP_THM] >> metis_tac[rtc_mono1, rtc_mono2a, rtc_mono2b, rtc_mono2c]);

val seqDone_rtc = save_thm(
  "seqDone_rtc[simp]",
  seqDones_rtc |> Q.INST[`pfx` |-> `[Done]`]
               |> SIMP_RULE list_ss [])

val general_rtcseq_cases = save_thm(
  "general_rtcseq_cases",
  seqDones_rtc |> Q.INST [`pfx` |-> `[]`]
               |> SIMP_RULE list_ss []);

val labelled_done = store_thm(
  "labelled_done[simp]",
  ``(m, labelled vs Done) --->* (m, Done)``,
  Induct_on `vs` >> simp[] >> qx_gen_tac `v` >>
  match_mp_tac (RTC_RULES_RIGHT1 |> SPEC_ALL |> CONJUNCT2) >>
  qexists_tac `(m, Label v Done)` >> reverse conj_tac >- e1tac >>
  simp[labelled_RTC_mono |> SPEC_ALL |> Q.INST [`vs` |-> `[v]`]
                         |> SIMP_RULE (srw_ss()) []]);

val Label_RTC_mono = save_thm(
  "Label_RTC_mono[simp]",
  labelled_RTC_mono |> SPEC_ALL |> Q.INST [`vs` |-> `[v]`]
                    |> SIMP_RULE (srw_ss()) [])

val Label_Done = save_thm(
  "Label_Done[simp]",
  labelled_done |> Q.INST [`vs` |-> `[v]`]
                |> SIMP_RULE list_ss [])

val labelled_abort1 = store_thm(
  "labelled_abort1[simp]",
  ``(m, labelled vs Abort) --->* (m, Abort)``,
  Induct_on `vs` >> simp[] >> qx_gen_tac `v` >>
  match_mp_tac (RTC_RULES_RIGHT1 |> SPEC_ALL |> CONJUNCT2) >>
  qexists_tac `(m, Label v Abort)` >> reverse conj_tac >- e1tac >>
  simp[labelled_RTC_mono |> SPEC_ALL |> Q.INST [`vs` |-> `[v]`]
                         |> SIMP_RULE (srw_ss()) []]);

val Label_abort = store_thm(
  "Label_abort[simp]",
  ``(m0, Label v s) --->* (m, Abort) ⇔ (m0, s) --->* (m, Abort)``,
  eq_tac
  >- (strip_tac >>
      `(∃x0. (m0, Label v s) = x0) ∧ ∃x. (m,Abort) = x`  by simp[] >>
      fs[] >> ntac 2 (pop_assum mp_tac) >>
      map_every qid_spec_tac [`m0`, `v`, `s`, `m`] >> pop_assum mp_tac >>
      map_every qid_spec_tac [`x`, `x0`] >>
      ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rpt strip_tac >> rw[] >>
      qpat_assum `(m0, Label v s) ---> x` mp_tac >>
      simp[Once eval_cases] >> simp[] >> rw[] >> fs[] >> metis_tac[RTC_RULES]) >>
  strip_tac >>
  match_mp_tac (RTC_RULES_RIGHT1 |> SPEC_ALL |> CONJUNCT2) >>
  qexists_tac `(m, Label v Abort)` >> reverse conj_tac >- e1tac >>
  metis_tac[labelled_RTC_mono,FOLDR]);

val labelled_abort2 = store_thm(
  "labelled_abort2[simp]",
  ``∀vs. (m0, labelled vs s) --->* (m, Abort) ⇔ (m0, s) --->* (m, Abort)``,
  Induct >> simp[]);

val ParDone = store_thm(
  "ParDone[simp]",
  ``(m0, Par(Done::sts)) ---> (m, res) ⇔
      res = Done ∧ m = m0 ∧ EVERY ($= Done) sts ∨
      res = Abort ∧ m = m0 ∧ MEM Abort sts ∨
      ∃sts'. res = Par(Done::sts') ∧ (m0, Par sts) ---> (m, Par sts')``,
  ONCE_REWRITE_TAC [eval_cases] >> simp[] >> Cases_on `res = Abort` >> simp[] >>
  Cases_on `res = Done` >> simp[] >> eq_tac >> rw[]
  >- (RULE_ASSUM_TAC (SIMP_RULE (srw_ss())[APPEND_EQ_CONS]) >>
      POP_ASSUM_LIST (map_every strip_assume_tac) >> rw[] >> fs[] >>
      metis_tac[]) >>
  metis_tac[APPEND])

val ParRTCDone_I = store_thm(
  "ParRTCDone_I",
  ``(m0, Par sts) --->* (m, Done) ⇒
    (m0, Par(Done :: sts)) --->* (m, Done)``,
  `∀x0 x. x0 --->* x ⇒
          ∀m0 sts m. x0 = (m0, Par sts) ∧ x = (m, Done) ⇒
                     (m0,Par(Done::sts)) --->* (m, Done)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rw[] >>
  qpat_assum `(m0, Par sts) ---> x` mp_tac >>
  simp[Once eval_cases] >> rw[] >> fs[] >>
  metis_tac[eval_rules, RTC_RULES, APPEND]);

val RINTER_RTC_E = store_thm(
  "RINTER_RTC_E",
  ``!x y. (R1 RINTER R2)^* x y ==> R1^* x y /\ R2^* x y``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC[][RINTER] THEN
  METIS_TAC [RTC_RULES]);

val transitive_RTC_R = store_thm(
  "transitive_RTC_R",
  ``reflexive R ∧ transitive R ⇒ RTC R = R``,
  SRW_TAC [][reflexive_def, transitive_def] THEN
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, FORALL_AND_THM, EQ_IMP_THM] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN METIS_TAC[]);

val strip_label_simulation1 = prove(
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      ∀c0'. strip_label c0' = strip_label c0 ⇒
            ∃c'. (m0,c0') --->* (m,c') ∧
                 strip_label c' = strip_label c``,
  ho_match_mp_tac eval_ind' >> simp[] >> rpt conj_tac >>
  TRY (simp[PULL_EXISTS] >> rpt strip_tac >> qexists_tac `vs` >>
       match_mp_tac labelled_RTC_mono >> etac)
  >- (simp[PULL_EXISTS, MAP_EQ_APPEND, MAP_EQ_CONS] >>
      qx_genl_tac [`c`, `c0`, `pfx`, `sfx`, `m0`, `m`] >> rpt strip_tac >>
      qmatch_assum_rename_tac `MAP strip_label pfx = MAP strip_label pf'` >>
      qmatch_assum_rename_tac `MAP strip_label sfx = MAP strip_label sf'` >>
      qmatch_assum_rename_tac `strip_label c0 = strip_label c0'` >>
      `∃c'. (m0,c0') --->* (m,c') ∧ strip_label c' = strip_label c`
        by metis_tac[] >>
      map_every qexists_tac [`vs`, `sf'`, `pfx`, `c'`] >> simp[] >>
      match_mp_tac labelled_RTC_mono >>
      `(m0,Seq (pf' ++ [c0'] ++ sf')) --->* (m0, Seq (pfx ++ [c0'] ++ sf'))`
        by (Q.UNDISCH_THEN `EVERY ($= Done) pfx` mp_tac >>
            Q.UNDISCH_THEN `MAP strip_label pfx = MAP strip_label pf'` mp_tac >>
            simp_tac bool_ss [GSYM APPEND_ASSOC] >>
            qspec_tac (`[c0'] ++ sf'`, `tl`) >>
            map_every qid_spec_tac [`pfx`, `pf'`] >>
            rpt (pop_assum kall_tac) >> Induct >>
            simp[MAP_EQ_CONS, PULL_EXISTS] >> qx_genl_tac [`tl`, `pft`, `vs`] >>
            rpt strip_tac >>
            `(m0, Seq(labelled vs Done::(pf' ++ tl))) --->*
             (m0,Seq(Done::(pf'++tl)))`
              by (match_mp_tac (evalrtc_seq |> Q.INST [`pfx` |-> `[]`]
                                            |> SIMP_RULE (srw_ss()) []) >>
                  Induct_on `vs` >> simp[] >> qx_gen_tac `v` >>
                  `(m0, Label v Done) ---> (m0, Done)` by e1tac >>
                  IMP_RES_THEN (qspec_then `[v]` mp_tac) labelled_RTC_mono >>
                  simp[] >> metis_tac[RTC_RULES_RIGHT1]) >>
            `(m0, Seq (Done::(pf' ++ tl))) --->* (m0, Seq(Done::(pft++tl)))`
              suffices_by metis_tac[RTC_CASES_RTC_TWICE] >>
            simp[]) >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0,Seq(pfx ++ [c0'] ++ sf'))` >> simp[] >>
      simp[evalrtc_seq])
  >- (simp[PULL_EXISTS] >> rpt strip_tac >> qexists_tac `[]` >> simp[] >>
      `MAP strip_label cs = cs`
        by (pop_assum kall_tac >> Induct_on `cs` >> simp[]) >>
      pop_assum SUBST_ALL_TAC >> rw[] >>
      fs[MEM_MAP, EVERY_MEM, PULL_EXISTS] >>
      `(m0, labelled vs (Seq sts')) --->* (m0, labelled vs Done)`
        by (match_mp_tac labelled_RTC_mono >> Induct_on `sts'` >>
            simp[] >- etac >> dsimp[] >> rpt strip_tac >> fs[] >>
            simp[Once RTC_CASES_RTC_TWICE] >>
            qexists_tac `(m0, Seq (Done :: sts'))` >> simp[] >>
            match_mp_tac (evalrtc_seq |> Q.INST [`pfx` |-> `[]`]
                                      |> SIMP_RULE (srw_ss()) []) >>
            simp[]) >>
      `(m0, labelled vs Done) --->* (m0, Done)` by simp[] >>
      metis_tac[RTC_CASES_RTC_TWICE])
  >- (simp[PULL_EXISTS, MAP_EQ_APPEND, MAP_EQ_CONS] >>
      qx_genl_tac [`m0`, `pfx`, `sfx`] >> strip_tac >>
      qx_genl_tac [`vs`, `sf'`, `pf'`, `vs'`] >> rpt strip_tac >>
      qexists_tac `vs` >> match_mp_tac labelled_RTC_mono >>
      `(m0,Seq (pf' ++ [labelled vs' Abort] ++ sf')) --->*
       (m0,Seq (pfx ++ [labelled vs' Abort] ++ sf'))`
        by (Q.UNDISCH_THEN `EVERY ($= Done) pfx` mp_tac >>
            Q.UNDISCH_THEN `MAP strip_label pfx = MAP strip_label pf'` mp_tac >>
            simp_tac bool_ss [GSYM APPEND_ASSOC] >>
            qspec_tac (`[labelled vs' Abort] ++ sf'`, `tl`) >>
            map_every qid_spec_tac [`pfx`, `pf'`] >>
            rpt (pop_assum kall_tac) >> Induct >>
            simp[MAP_EQ_CONS, PULL_EXISTS] >> qx_genl_tac [`tl`, `pft`, `vs`] >>
            rpt strip_tac >>
            `(m0, Seq(labelled vs Done::(pf' ++ tl))) --->*
             (m0,Seq(Done::(pf'++tl)))`
              by (match_mp_tac (evalrtc_seq |> Q.INST [`pfx` |-> `[]`]
                                            |> SIMP_RULE (srw_ss()) []) >>
                  Induct_on `vs` >> simp[] >> qx_gen_tac `v` >>
                  `(m0, Label v Done) ---> (m0, Done)` by e1tac >>
                  IMP_RES_THEN (qspec_then `[v]` mp_tac) labelled_RTC_mono >>
                  simp[] >> metis_tac[RTC_RULES_RIGHT1]) >>
            `(m0, Seq (Done::(pf' ++ tl))) --->* (m0, Seq(Done::(pft++tl)))`
              suffices_by metis_tac[RTC_CASES_RTC_TWICE] >>
            simp[]) >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0,Seq(pfx ++ [labelled vs' Abort] ++ sf'))` >> simp[] >>
      asm_simp_tac bool_ss [seqDones_rtc, GSYM APPEND_ASSOC] >> simp[] >>
      rpt (pop_assum kall_tac) >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0, Seq (Abort::sf'))`>> reverse conj_tac
      >- (match_mp_tac RTC_SUBSET >> simp[Once eval_cases] >>
          qexists_tac `[]` >> simp[]) >>
      match_mp_tac (evalrtc_seq |> Q.INST [`pfx` |-> `[]`]
                                |> SIMP_RULE (srw_ss()) []) >>
      simp[])
  >- (simp[PULL_EXISTS, MAP_EQ_CONS] >> rpt strip_tac >>
      map_every qexists_tac [`vs`, `if b then t' else e'`, `[]`] >>
      simp[] >> ONCE_REWRITE_TAC [COND_RAND] >> rw[] >>
      match_mp_tac labelled_RTC_mono >> match_mp_tac RTC_SUBSET >>
      e1tac)
  >- (simp[PULL_EXISTS] >> rpt strip_tac >>
      map_every qexists_tac [
        `vs`, `MAP (λdv. Label dv (ssubst vnm dv s')) iters`
      ] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
      match_mp_tac labelled_RTC_mono >> etac)
  >- (simp[PULL_EXISTS] >> rpt strip_tac >>
      map_every qexists_tac [
        `vs`, `MAP (λdv. Label dv (ssubst vnm dv s')) iters`
      ] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
      match_mp_tac labelled_RTC_mono >> etac)
  >- (simp[PULL_EXISTS] >> rpt strip_tac >>
      pop_assum mp_tac >>
      simp[SimpL ``$==>``, MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      qmatch_assum_rename_tac `MAP strip_label pfx = MAP strip_label p'` >>
      qmatch_assum_rename_tac `MAP strip_label sfx = MAP strip_label s'` >>
      qmatch_assum_rename_tac `strip_label c0 = strip_label c0'` >>
      `∃c'. (m0,c0') --->* (m,c') ∧ strip_label c' = strip_label c`
        by metis_tac[] >>
      map_every qexists_tac [`vs`, `p' ++ [c'] ++ s'`] >> simp[] >>
      match_mp_tac labelled_RTC_mono >> match_mp_tac evalrtc_par >> simp[])
  >- (simp[PULL_EXISTS] >> rpt strip_tac >> qexists_tac `vs` >>
      match_mp_tac labelled_RTC_mono >>
      `MAP strip_label cs = cs`
        by (pop_assum kall_tac >> Induct_on `cs` >> simp[]) >>
      pop_assum SUBST_ALL_TAC >> rw[] >> fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
      Induct_on `sts'` >> simp[] >- etac >> dsimp[] >> rpt strip_tac >> fs[] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0, Par(Done::sts'))` >>
      simp[ParRTCDone_I] >> rpt (pop_assum kall_tac) >>
      match_mp_tac (evalrtc_par |> Q.INST [`pfx` |-> `[]`]
                                |> SIMP_RULE (srw_ss()) []) >>
      Induct_on `vs` >> simp[])
  >- (simp[PULL_EXISTS] >> rpt strip_tac >>
      qexists_tac `vs` >> simp[] >> match_mp_tac labelled_RTC_mono >>
      fs[Once MEM_SPLIT_APPEND_first] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qmatch_assum_rename_tac `MAP strip_label pfx = MAP strip_label p'` >>
      qmatch_assum_rename_tac `MAP strip_label sfx = MAP strip_label s'` >>
      qexists_tac `(m0, Par (p' ++ [Abort] ++ s'))` >> reverse conj_tac >- etac>>
      match_mp_tac evalrtc_par >> simp[])
  >- ((* while *) simp[PULL_EXISTS, MAP_EQ_CONS] >>
      qx_genl_tac [`g`, `b`, `m0`, `vs`, `b'`] >> strip_tac >>
      map_every qexists_tac [`vs`, `[]`, `[]`, `b'`, `[]`, `b'`] >>
      simp[] >> match_mp_tac labelled_RTC_mono >>
      match_mp_tac RTC_SUBSET >> e1tac)
  >- (simp[PULL_EXISTS] >> qx_genl_tac [`m0`, `s`, `m`] >>
      strip_tac >>
      qmatch_assum_abbrev_tac `eR^* (m0,s) (m,Done)` >>
      qabbrev_tac `
        R = λ(m0,s0) (m,s).
             ∀c. strip_label c = strip_label s0 ⇒
                 ∃c'. (m0,c) --->* (m,c') ∧
                      strip_label c' = strip_label s` >>
      `eR = eval RINTER R`
        by simp[FUN_EQ_THM, Abbr`eR`, Abbr`R`, RINTER, FORALL_PROD] >>
      Q.RM_ABBREV_TAC `eR` >> pop_assum SUBST_ALL_TAC >>
      imp_res_tac RINTER_RTC_E >>
      `reflexive R /\ transitive R`
        by (simp[transitive_def, Abbr`R`, FORALL_PROD, reflexive_def] >>
            metis_tac[RTC_RTC, RTC_RULES]) >>
      `RTC R = R` by metis_tac[transitive_RTC_R] >> pop_assum SUBST_ALL_TAC >>
      qunabbrev_tac `R` >> fs[] >> qx_genl_tac [`vs`, `s'`] >> strip_tac >>
      qexists_tac `vs` >> match_mp_tac labelled_RTC_mono >>
      match_mp_tac RTC_SUBSET >>
      `∃s'' vs'. (m0,s') --->* (m,s'') ∧ s'' = labelled vs' Done`
        by metis_tac[] >>
      `(m, labelled vs' Done) --->* (m, Done)` by simp[] >> rw[] >>
      `(m0, s') --->* (m, Done)` by metis_tac[RTC_RTC] >>
      e1tac)
  >- (simp[PULL_EXISTS] >> rpt strip_tac >>
      qexists_tac `labelled vs (ssubst vnm (evalexpr m0 e) s')` >> simp[] >>
      match_mp_tac labelled_RTC_mono >>
      match_mp_tac RTC_SUBSET >> simp[Once eval_cases])
);

val eval_strip_label_I = save_thm(
  "eval_strip_label_I",
  strip_label_simulation1
    |> SPEC_ALL |> UNDISCH |> SPEC ``strip_label c0``
    |> SIMP_RULE (srw_ss()) [] |> DISCH_ALL);

val strip_label_simulation0 = prove(
  ``∀x0 x. x0 --->* x ⇒
           ∀m0 c0 c0' m c.
             x0 = (m0,c0) ∧ x = (m,c) ∧
             strip_label c0' = strip_label c0 ⇒
             ∃c'. (m0,c0') --->* (m,c') ∧ strip_label c' = strip_label c``,
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rw[]
  >- metis_tac [RTC_RULES] >>
  qmatch_assum_rename_tac `(m0,c0) ---> mc'` >>
  `∃m' c'. mc' = (m',c')` by (Cases_on `mc'` >> simp[]) >> rw[] >>
  `∃c''. (m0, c0') --->* (m', c'') ∧ strip_label c'' = strip_label c'`
    by metis_tac[strip_label_simulation1] >>
  `∃cc. (m',c'') --->* (m,cc) ∧ strip_label cc = strip_label c`
    by metis_tac[] >>
  metis_tac[RTC_CASES_RTC_TWICE])

val strip_label_bisimulation = save_thm(
  "strip_label_bisimulation",
  strip_label_simulation0
    |> SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO]);

open monadsyntax

(* opt_sequence : (α option) list -> α list option *)
val OPT_SEQUENCE_def = Define`
  (OPT_SEQUENCE [] = SOME []) ∧
  (OPT_SEQUENCE (h :: t) = lift2 CONS h (OPT_SEQUENCE t))
`;

val _ = augment_srw_ss [
  rewrites [SIMP_RULE (bool_ss ++ ETA_ss) [] FINITE_BAG_FOLDR_loopbag]
]

val MEM_FOLDR_mlt = store_thm(
  "MEM_FOLDR_mlt",
  ``MEM e l ⇒
    mlt $< (loopbag (f e)) (FOLDR (\e a. loopbag (f e) ⊎ a) {||} l) ∨
    loopbag (f e) = FOLDR (\e a. loopbag (f e) ⊎ a) {||} l``,
  simp[] >> Induct_on `l` >> dsimp[] >> rpt strip_tac >> res_tac
  >- (Cases_on `loopbag (f h) = {||}` >> simp[] >>
      disj1_tac >>
      qmatch_abbrev_tac `mlt $< (loopbag (f e)) (loopbag (f h) ⊎ FF)` >>
      `mlt $< FF (loopbag (f h) ⊎ FF)` by simp[Abbr`FF`] >>
      metis_tac[TC_RULES]) >>
  pop_assum SUBST_ALL_TAC >> simp[]);

val _ = type_abbrev("actionRW", ``:string # num list``)

val _ = overload_on ("actRWName", ``FST : actionRW -> string``)

val arrayError_def = Define`
  arrayError (Array _) = Error ∧
  arrayError v = v
`;
val _ = export_rewrites ["arrayError_def"]

val lookupRW_def = Define`
  lookupRW m (a, ns) =
    arrayError
      (evalmaccess m (FOLDL (λa n. ASub a (Value (Int &n))) (VRead a) ns))
`;

val apply_action_def = Define`
  apply_action a m_opt =
    case a.write of
        NONE => m_opt
      | SOME w =>
        do
          m <- m_opt;
          vs <- SOME(MAP (lookupRW m) a.reads);
          value <- SOME (a.data vs);
          upd_memory w value m
        od
`;

val lift_OPTION_BIND = store_thm(
  "lift_OPTION_BIND",
  ``OPTION_BIND (OPTION_BIND v f) g =
    OPTION_BIND v (combin$C (OPTION_BIND o f) g)``,
  Cases_on `v` >> simp[]);

val upd_var_EQ_NONE = store_thm(
  "upd_var_EQ_NONE",
  ``upd_var m vnm v = NONE ⇔
      vnm ∉ FDOM m ∨ isArray (m ' vnm) ∨ v = Error ∨ isArray v``,
  rw[upd_var_def] >> metis_tac[]);

val updarray_EQ_NONE = store_thm(
  "updarray_EQ_NONE",
  ``upd_array m a i v = NONE ⇔
    ∀vlist. FLOOKUP m a = SOME (Array vlist) ⇒ i < 0 ∨ &LENGTH vlist ≤ i``,
  `FLOOKUP m a = NONE ∨ ∃v'. FLOOKUP m a = SOME v'`
    by metis_tac[option_CASES] >>
  simp[upd_array_def] >> Cases_on `v'` >> simp[]);

val upd_memory_preserves_FDOMs = store_thm(
  "upd_memory_preserves_FDOMs",
  ``upd_memory w value m = SOME m' ⇒ FDOM m' = FDOM m``,
  `(∃s. w = (s, [])) ∨ (∃s i is. w = (s, i::is))`
     by metis_tac[list_CASES, pair_CASES] >> simp[upd_memory_def, upd_var_def] >> rw[] >>
  simp[ABSORPTION_RWT] >>
  Cases_on `FLOOKUP m s` >> fs[] >>
  Cases_on `x` >> fs[] >> rw[] >>
  match_mp_tac ABSORPTION_RWT >>
  fs[FLOOKUP_DEF]);

val apply_action_preserves_FDOMs = store_thm(
  "apply_action_preserves_FDOMs",
  ``apply_action a (SOME m) = SOME m' ⇒ FDOM m' = FDOM m``,
  simp[apply_action_def] >> Cases_on `a.write` >> simp[] >>
  metis_tac[upd_memory_preserves_FDOMs]);

val upd_nested_array_preserves_array_length = store_thm(
  "upd_nested_array_preserves_array_length",
  ``upd_nested_array i is v l = SOME l' ⇒ LENGTH l' = LENGTH l``,
  Cases_on `is` >> simp[upd_nested_array_def, value_case_eq] >> rw[] >> simp[]);

val upd_memory_preserves_array_presence_length_back = store_thm(
  "upd_memory_preserves_array_presence_length_back",
  ``upd_memory w value m = SOME m' ∧ FLOOKUP m' a = SOME (Array els) ⇒
    ∃els'. FLOOKUP m a = SOME (Array els') ∧ LENGTH els' = LENGTH els``,
  `(∃s i is. w = (s, i::is)) ∨ (∃s. w = (s, []))`
    by metis_tac[list_CASES, pair_CASES] >>
  simp[upd_memory_def] >| [
    simp[option_case_eq, value_case_eq, PULL_EXISTS, FLOOKUP_DEF] >> rw[] >>
    fs[FAPPLY_FUPDATE_THM, bool_case_eq] >> veq >> fs[] >>
    metis_tac[upd_nested_array_preserves_array_length],
    rw[FLOOKUP_DEF, upd_var_def] >> fs[] >> rw[] >> fs[] >>
    fs[FAPPLY_FUPDATE_THM] >> pop_assum mp_tac >> rw[] >> fs[]
  ]);

val upd_nested_diamond_NONE_preserved = store_thm(
  "upd_nested_diamond_NONE_preserved",
  ``∀is1 i1 v1 vlist i2 is2 vlist'.
      upd_nested_array i1 is1 v1 vlist = NONE ∧
      upd_nested_array i2 is2 v2 vlist = SOME vlist' ⇒
      upd_nested_array i1 is1 v1 vlist' = NONE``,
  Induct
  >- (Cases_on `is2` >>
      simp[upd_nested_array_def, option_case_eq, value_case_eq] >>
      rpt strip_tac >> simp[] >> veq >> fs[] >>
      simp[EL_LUPDATE] >> rw[] >> fs[]) >>
  Cases_on `is2` >> simp[upd_nested_array_def, value_case_eq] >>
  rpt strip_tac >> simp[] >> veq >> fs[] >>
  Cases_on `i1 = i2` >> fs[EL_LUPDATE] >> veq >> metis_tac[])

val upd_memory_diamond_NONE_preserved = store_thm(
  "upd_memory_diamond_NONE_preserved",
  ``upd_memory w1 v1 m = NONE ∧ upd_memory w2 v2 m = SOME m' ⇒
    upd_memory w1 v1 m' = NONE``,
  `(∃s1 i1 is1. w1 = (s1, i1::is1)) ∨ (∃s1. w1 = (s1, []))`
    by metis_tac[list_CASES, pair_CASES] >>
  `(∃s2 i2 is2. w2 = (s2, i2::is2)) ∨ (∃s2. w2 = (s2, []))`
    by metis_tac[list_CASES, pair_CASES] >>
  simp[upd_memory_def, option_case_eq, value_case_eq, FLOOKUP_DEF, PULL_EXISTS,
       upd_var_def] >>
  rpt strip_tac >> simp[] >> veq >> csimp[FAPPLY_FUPDATE_THM, bool_case_eq] >>
  Cases_on `s1 = s2` >> fs[] >> veq >> simp[]
  >- metis_tac[upd_nested_diamond_NONE_preserved] >>
  Cases_on `v2` >> fs[]);

val lookup_indices_def = Define`
  (lookup_indices v [] = v) ∧
  (lookup_indices (Array vlist) (i::is) =
     if i < LENGTH vlist then lookup_indices (EL i vlist) is
     else Error) ∧
  (lookup_indices _ (i::is) = Error)`
val _ = export_rewrites ["lookup_indices_def"]

val lookup_indices_error = store_thm(
  "lookup_indices_error[simp]",
  ``lookup_indices Error is = Error``,
  Cases_on `is` >> simp[]);

val lookupRW_lookup_indices = store_thm(
  "lookupRW_lookup_indices",
  ``lookupRW m (a, is) =
     arrayError (lookup_indices (evalmaccess m (VRead a)) is)``,
  simp[lookupRW_def] >> AP_TERM_TAC >> qspec_tac(`VRead a`, `ma`) >>
  Induct_on `is` >> simp[evalexpr_def] >>
  Cases_on `evalmaccess m ma` >> simp[] >>
  rw[] >> lfs[]);

val lookupRW_FUPDATE = store_thm(
  "lookupRW_FUPDATE",
  ``lookupRW (m |+ (nm1, v)) (nm2, is) =
      if nm1 = nm2 then arrayError (lookup_indices v is)
      else lookupRW m (nm2, is)``,
  simp[lookupRW_lookup_indices] >>
  rw[evalexpr_def, lookup_v_def, FLOOKUP_DEF, DOMSUB_FAPPLY_THM,
     FAPPLY_FUPDATE_THM] >> fs[]);

val upd_nested_array_EL = store_thm(
  "upd_nested_array_EL",
  ``∀is i value vlist vlist'.
      upd_nested_array i is value vlist = SOME vlist' ∧ i ≠ j ⇒
      EL j vlist' = EL j vlist``,
  Cases >> dsimp[upd_nested_array_def, option_case_eq, value_case_eq,
                 EL_LUPDATE]);

val lookup_indices_nonarray = store_thm(
  "lookup_indices_nonarray",
  ``¬isArray v ⇒ (lookup_indices v js = if js = [] then v else Error)``,
  Cases_on `v` >> Cases_on `js` >> simp[]);

val upd_nested_lookup_indices_EL = store_thm(
  "upd_nested_lookup_indices_EL",
  ``∀is i js vlist vlist'.
      upd_nested_array i is value vlist = SOME vlist' ∧ is ≠ js ⇒
      arrayError (lookup_indices (EL i vlist') js) =
      arrayError (lookup_indices (EL i vlist) js)``,
  Induct >> simp[upd_nested_array_def, value_case_eq]
  >- (rw[] >> simp[EL_LUPDATE, lookup_indices_nonarray]) >>
  dsimp[EL_LUPDATE] >> qx_genl_tac [`i'`, `i`, `js`] >>
  `js = [] ∨ ∃j js0. js = j::js0` by (Cases_on `js` >> simp[]) >>
  simp[] >> rpt gen_tac >> reverse (Cases_on `i' = j`) >> simp[]
  >- (strip_tac >>
      imp_res_tac upd_nested_array_preserves_array_length >> simp[] >>
      rw[] >> metis_tac[upd_nested_array_EL]) >>
  metis_tac[upd_nested_array_preserves_array_length]);

val upd_nested_array_lookup_indices = store_thm(
  "upd_nested_array_lookup_indices",
  ``upd_nested_array i is value vlist = SOME vlist' ∧ js ≠ i::is ⇒
      arrayError (lookup_indices (Array vlist') js) =
      arrayError (lookup_indices (Array vlist) js)``,
  `js = [] ∨ ∃j js0. js = j::js0` by (Cases_on `js` >> simp[]) >> simp[] >>
  Cases_on `upd_nested_array i is value vlist = SOME vlist'` >> simp[] >>
  imp_res_tac upd_nested_array_preserves_array_length >> simp[] >>
  Cases_on `j < LENGTH vlist` >> simp[] >> reverse (Cases_on `j = i`) >>
  simp[] >- metis_tac[upd_nested_array_EL] >> rw[] >>
  metis_tac[upd_nested_lookup_indices_EL]);

val nontouching_updm_read_after_writes = store_thm(
  "nontouching_updm_read_after_writes",
  ``upd_memory w value m = SOME m' ∧ w ≠ rd ⇒ lookupRW m' rd = lookupRW m rd``,
  `(∃a i is. w = (a, i::is)) ∨ ∃s. w = (s,[])`
    by metis_tac[list_CASES, pair_CASES] >>
  `(∃b j js. rd = (b, j::js)) ∨ ∃t. rd = (t,[])`
    by metis_tac[list_CASES, pair_CASES] >>
  simp[upd_memory_def, option_case_eq, value_case_eq, PULL_EXISTS] >> rw[]
  >- (simp[lookupRW_FUPDATE])
  >- (Cases_on `a = b` >> simp[lookupRW_FUPDATE] >>
      simp[lookupRW_lookup_indices, evalexpr_def, lookup_v_def] >> fs[] >>
      imp_res_tac upd_nested_array_preserves_array_length >> simp[] >> rw[] >>
      metis_tac[upd_nested_array_EL])
  >- (Cases_on `a = b` >> simp[lookupRW_FUPDATE] >>
      simp[lookupRW_lookup_indices, evalexpr_def, lookup_v_def] >> fs[] >>
      imp_res_tac upd_nested_array_preserves_array_length >> simp[] >> rw[] >>
      reverse (Cases_on `i = j`) >- metis_tac[upd_nested_array_EL] >> rw[] >>
      metis_tac[upd_nested_lookup_indices_EL])
  >- (Cases_on `a = t` >> simp[lookupRW_FUPDATE] >> rw[] >>
      simp[lookupRW_lookup_indices, evalexpr_def, lookup_v_def])
  >- (fs[upd_var_def] >> rw[lookupRW_FUPDATE] >>
      simp[lookupRW_lookup_indices, evalexpr_def, lookup_v_def,
           FLOOKUP_DEF, lookup_indices_nonarray])
  >- (fs[upd_var_def] >> rw[lookupRW_FUPDATE]))

val nontouching_updm_expreval = store_thm(
  "nontouching_updm_expreval",
  ``a1 ≁ₜ a2 ∧ a2.write = SOME w ∧ upd_memory w value m = SOME m' ⇒
    MAP (lookupRW m') a1.reads = MAP (lookupRW m) a1.reads``,
  simp[MAP_EQ_f] >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  `r ≠ w` by (fs[touches_def] >> metis_tac[]) >>
  metis_tac[nontouching_updm_read_after_writes]);

val FLOOKUP_memory_cases = prove(
  ``!x: value option.
      x = NONE ∨ (∃i. x = SOME (Int i)) ∨ (∃r. x = SOME (Real r)) ∨
      (∃vl. x = SOME (Array vl)) ∨ (∃b. x = SOME (Bool b)) ∨
      x = SOME Error``,
  metis_tac[option_CASES, TypeBase.nchotomy_of ``:value``]);

val flookupmem_t = ``FLOOKUP (m:memory) s``
val matches_flookupmem = can (match_term flookupmem_t)
fun flookupmem_tac (g as (asl,w)) = let
  val t = find_term matches_flookupmem w
in
  STRIP_ASSUME_TAC (SPEC t FLOOKUP_memory_cases) g
end

val updm_VAR_SOME_EQN = store_thm(
  "updm_VAR_SOME_EQN",
  ``upd_memory (s, []) v m = SOME m' ⇔
    ¬isArray v ∧ s ∈ FDOM m ∧ ¬isArray (m ' s) ∧ v ≠ Error ∧ m' = m |+ (s,v)``,
  simp[upd_memory_def, upd_var_def] >> metis_tac[]);

fun disjneq_search (g as (asl,w)) = let
  val ds = strip_disj w
  fun is_neq t = is_eq (dest_neg t) handle HOL_ERR _ => false
in
  case List.find is_neq ds of
      NONE => NO_TAC
    | SOME d => ASM_CASES_TAC (dest_neg d) THEN ASM_REWRITE_TAC[]
end g

fun has_cond t = can (find_term (same_const ``COND``)) t

val valid_vallookup_def = Define`
  (valid_vallookup (Array vlist) [] ⇔ F) ∧
  (valid_vallookup (Array vlist) (i::is) ⇔
     i < LENGTH vlist ∧ valid_vallookup (EL i vlist) is) ∧
  (valid_vallookup _ l ⇔ l = [])
`;
val _ = export_rewrites ["valid_vallookup_def"]

val valid_lvalue_def = Define`
  valid_lvalue m = {(vnm, is) | vnm ∈ FDOM m ∧ valid_vallookup (m ' vnm) is}
`;

val valid_lvalue_BIGUNION = store_thm(
  "valid_lvalue_BIGUNION",
  ``valid_lvalue m =
      BIGUNION (IMAGE (λvnm. { (vnm,is) | is | valid_vallookup (m ' vnm) is })
                      (FDOM m))``,
  dsimp[valid_lvalue_def, Once EXTENSION] >> metis_tac[]);

val valid_vallookup_Array = store_thm(
  "valid_vallookup_Array[simp]",
  ``valid_vallookup (Array vl) is ⇔
    ∃i0 is0. is = i0 :: is0 ∧ i0 < LENGTH vl ∧
             valid_vallookup (EL i0 vl) is0``,
  Cases_on `is` >> simp[])

val FINITE_valid_vallookup = store_thm(
  "FINITE_valid_vallookup[simp]",
  ``FINITE { is | valid_vallookup v is }``,
  completeInduct_on `value_size v` >> fs[PULL_FORALL] >> rw[] >>
  Cases_on `v` >> simp[] >>
  qmatch_abbrev_tac `FINITE someset` >>
  `someset =
    BIGUNION (IMAGE (λn. { n :: is0 | is0 | valid_vallookup (EL n l) is0 })
                    (count (LENGTH l)))`
    by (dsimp[Once EXTENSION, Abbr`someset`] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> dsimp[] >> qx_gen_tac `n` >> strip_tac >>
  qmatch_abbrev_tac `FINITE otherset` >>
  `otherset = IMAGE (CONS n) {is0 | valid_vallookup (EL n l) is0}`
    by simp[EXTENSION, Abbr`otherset`] >> simp[] >>
  first_x_assum match_mp_tac >> Q.UNDISCH_THEN `n < LENGTH l` mp_tac >>
  map_every qid_spec_tac [`n`, `l`] >> rpt (pop_assum kall_tac) >>
  Induct >> simp[value_size_def] >> qx_genl_tac [`e`, `n`] >>
  Cases_on `n` >> simp[] >> rw[] >> res_tac >> lfs[value_size_def]);

val FINITE_validlvalue = store_thm(
  "FINITE_valid_lvalue[simp]",
  ``FINITE (valid_lvalue m)``,
  dsimp[valid_lvalue_BIGUNION] >> rw[] >>
  qmatch_abbrev_tac `FINITE s` >>
  `s = IMAGE (λi. (vnm,i)) { is | valid_vallookup (m ' vnm) is}`
    suffices_by simp[] >>
  simp[EXTENSION, Abbr`s`]);

val lvalfmap_def = Define`
  lvalfmap m = FUN_FMAP (lookupRW m) (valid_lvalue m)
`;

val wfvalue_def = tDefine "wfvalue" `
  (wfvalue (Array l) ⇔ 0 < LENGTH l ∧ ∀n. n < LENGTH l ⇒ wfvalue (EL n l)) ∧
  (wfvalue _ ⇔ T)
` (WF_REL_TAC `measure value_size` >> Induct >> dsimp[LT_SUC, value_size_def] >>
   rpt strip_tac >> res_tac >> simp[])

val wfm_def = Define`
  wfm m ⇔ ∀k. k ∈ FDOM m ⇒ wfvalue (m ' k)
`;

val domain_extends_to_validlvalues = store_thm(
  "domain_extends_to_validlvalues",
  ``∀nm m. wfm m ∧ nm ∈ FDOM m ⇒ ∃is. valid_lvalue m (nm,is)``,
  simp[valid_lvalue_def, EXISTS_PROD, wfm_def] >>
  `∀v. wfvalue v ⇒ ∃is. valid_vallookup v is` suffices_by metis_tac[] >>
  gen_tac >> completeInduct_on `value_size v` >>
  fs[PULL_FORALL, AND_IMP_INTRO] >> rw[] >> Cases_on `v` >> simp[] >>
  fs[wfvalue_def] >> qexists_tac `0` >> simp[] >> first_x_assum match_mp_tac >>
  reverse conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Q.UNDISCH_THEN `0 < LENGTH l` mp_tac >> qid_spec_tac `l` >>
  Induct >> simp[value_size_def]);

val valid_vallookup_NIL = store_thm(
  "valid_vallookup_NIL[simp]",
  ``valid_vallookup v [] = ¬isArray v``,
  Cases_on `v` >> simp[]);

val valid_vallookup_notArray = store_thm(
  "valid_vallookup_notArray",
  ``¬isArray v ⇒ (valid_vallookup v is ⇔ is = [])``,
  Cases_on `is` >> Cases_on `v` >> simp[]);

val upd_nested_array_Array = store_thm(
  "upd_nested_array_Array[simp]",
  ``∀i vl1 vl2. upd_nested_array i is (Array vl1) vl2 = NONE``,
  Induct_on `is` >> simp[upd_nested_array_def, value_case_eq] >>
  metis_tac[TypeBase.nchotomy_of ``:value``]);

val upd_memory_Array = store_thm(
  "upd_memory_Array",
  ``isArray v ⇒ upd_memory lv v m = NONE``,
  Cases_on `v` >> simp[] >>
  `∃vnm is. lv = (vnm, is)` by (Cases_on `lv` >> simp[]) >>
  `is = [] ∨ ∃i is0. is = i::is0` by (Cases_on `is` >> simp[]) >>
  simp[upd_memory_def, upd_var_def, option_case_eq, value_case_eq,
       FLOOKUP_DEF] >>
  Cases_on `vnm ∈ FDOM m` >> simp[] >>
  Cases_on `m ' vnm` >> simp[]);

val upd_nested_Error = store_thm(
  "upd_nested_Error[simp]",
  ``∀is i vl. upd_nested_array i is Error vl = NONE``,
  Induct >> simp[value_case_eq] >> metis_tac[TypeBase.nchotomy_of ``:value``]);

val upd_memory_Error = store_thm(
  "upd_memory_Error[simp]",
  ``upd_memory lv Error m = NONE``,
  `∃vnm is. lv = (vnm, is)` by (Cases_on `lv` >> simp[]) >>
  `is = [] ∨ ∃i is0. is = i::is0` by (Cases_on `is` >> simp[]) >>
  simp[upd_var_def, option_case_eq, value_case_eq, FLOOKUP_DEF] >>
  metis_tac[TypeBase.nchotomy_of ``:value``]);

val LUPDATE_commutes = store_thm(
  "LUPDATE_commutes",
  ``i ≠ j ⇒ LUPDATE u i (LUPDATE v j l) = LUPDATE v j (LUPDATE u i l)``,
  simp[LIST_EQ_REWRITE, EL_LUPDATE] >> rw[] >> rw[]);

val LUPDATE_override = store_thm(
  "LUPDATE_override[simp]",
  ``LUPDATE v1 i (LUPDATE v2 i l) = LUPDATE v1 i l``,
  simp[LIST_EQ_REWRITE, EL_LUPDATE]);

val _ = print "Big case split proof here - takes a little while\n"
val successful_upd_nested_diamond1 = store_thm(
  "successful_upd_nested_diamond1",
  ``upd_nested_array i is u vlist = SOME vlist1 ∧
    upd_nested_array j js v vlist = SOME vlist2 ∧
    i ≠ j ⇒
    ∃vlist.
      upd_nested_array j js v vlist1 = SOME vlist ∧
      upd_nested_array i is u vlist2 = SOME vlist``,
  Cases_on `is` >> Cases_on `js` >>
  simp[option_case_eq, value_case_eq] >>
  strip_tac >> veq >> simp[EL_LUPDATE, LUPDATE_commutes]);

val successful_upd_nested_diamond2 = store_thm(
  "successful_upd_nested_diamond2",
  ``∀is js i j u v vlist vlist1 vlist2.
      upd_nested_array i is u vlist = SOME vlist1 ∧
      upd_nested_array j js v vlist = SOME vlist2 ∧
      is ≠ js ⇒
      ∃vlist.
        upd_nested_array j js v vlist1 = SOME vlist ∧
        upd_nested_array i is u vlist2 = SOME vlist``,
  Induct
  >- (Cases_on `js` >> simp[option_case_eq, value_case_eq] >>
      rpt strip_tac >> veq >> simp[EL_LUPDATE, bool_case_eq] >>
      csimp[LUPDATE_commutes] >> strip_tac >> fs[]) >>
  qx_gen_tac `i0` >> rpt gen_tac >> reverse (Cases_on `i = j`)
  >- metis_tac[successful_upd_nested_diamond1] >>
  veq >> Cases_on `js` >>
  simp[option_case_eq, value_case_eq] >> strip_tac >> veq >> simp[] >>
  fs[] >> veq >> simp[EL_LUPDATE, PULL_EXISTS]
  >- metis_tac[successful_upd_nested_diamond1] >>
  metis_tac[])

val successful_upd_memory_diamond = store_thm(
  "successful_upd_memory_diamond",
  ``upd_memory lv1 v1 (m0:memory) = SOME m1 ∧
    upd_memory lv2 v2 m0 = SOME m2 ∧ lv1 ≠ lv2 ⇒
    ∃m. upd_memory lv1 v1 m2 = SOME m ∧ upd_memory lv2 v2 m1 = SOME m``,
  `∃vnm1 is1. lv1 = (vnm1, is1)` by (Cases_on `lv1` >> simp[]) >>
  `∃vnm2 is2. lv2 = (vnm2, is2)` by (Cases_on `lv2` >> simp[]) >>
  simp[] >> reverse (Cases_on `vnm1 = vnm2`) >> simp[]
  >- (`is1 = [] ∨ ∃i1 is01. is1 = i1::is01` by (Cases_on `is1` >> simp[]) >>
      `is2 = [] ∨ ∃i2 is02. is2 = i2::is02` by (Cases_on `is2` >> simp[]) >>
      simp[upd_memory_def, upd_var_def, FLOOKUP_DEF, option_case_eq,
           value_case_eq] >> strip_tac >> veq >>
      simp[FUPDATE_COMMUTES, FAPPLY_FUPDATE_THM]) >>
  veq >>
  `is1 = [] ∨ ∃i1 is01. is1 = i1::is01` by (Cases_on `is1` >> simp[]) >>
  `is2 = [] ∨ ∃i2 is02. is2 = i2::is02` by (Cases_on `is2` >> simp[]) >>
  simp[FLOOKUP_DEF, upd_var_def, option_case_eq, value_case_eq] >>
  strip_tac >> veq >> fs[] >>
  simp[PULL_EXISTS] >> veq
  >- rfs[]
  >- metis_tac[successful_upd_nested_diamond1]
  >- metis_tac[successful_upd_nested_diamond2])

val FLOOKUP_EQ_NONE = store_thm(
  "FLOOKUP_EQ_NONE[simp]",
  ``FLOOKUP f k = NONE ⇔ k ∉ FDOM f``,
  simp[FLOOKUP_DEF]);

val upd_memory_writes_commute = store_thm(
  "upd_memory_writes_commute",
  ``w1 ≠ w2 ∧
    upd_memory w1 v1 (m0:memory) = SOME m11 ∧ upd_memory w2 v2 m11 = SOME m12 ∧
    upd_memory w2 v2 m0 = SOME m21 ∧ upd_memory w1 v1 m21 = SOME m22 ⇒
    m12 = m22``,
  metis_tac[successful_upd_memory_diamond, SOME_11]);

val apply_action_commutes = store_thm(
  "apply_action_commutes",
  ``a1:(value list -> value,actionRW,α)action ≁ₜ
    a2:(value list -> value,actionRW,α)action ⇒
    apply_action a2 (apply_action a1 m) = apply_action a1 (apply_action a2 m)``,
  strip_tac >>
  `m = NONE ∨ ∃gm. m = SOME gm` by metis_tac[option_CASES] >>
  simp[apply_action_def, lift_OPTION_BIND, combinTheory.o_ABS_R,
       o_UNCURRY_R, C_UNCURRY_L,
       combinTheory.C_ABS_L] >>
  `a1.write = NONE ∨ ∃w1. a1.write = SOME w1`
    by (Cases_on `a1.write` >> simp[]) >>
  `a2.write = NONE ∨ ∃w2. a2.write = SOME w2`
    by (Cases_on `a2.write` >> simp[]) >>
  simp[] >>
  qabbrev_tac `
    A1U = λm. upd_memory w1 (a1.data (MAP (lookupRW m) a1.reads)) m` >>
  qabbrev_tac `
    A2U = λm. upd_memory w2 (a2.data (MAP (lookupRW m) a2.reads)) m` >>
  simp[] >>
  Cases_on `A1U gm` >> simp[]
  >- (Cases_on `A2U gm` >> simp[] >>
      qmatch_assum_rename_tac `A2U gm = SOME m'` >>
      fs[Abbr`A1U`, Abbr`A2U`] >>
      `MAP (lookupRW m') a1.reads = MAP (lookupRW gm) a1.reads`
        by metis_tac[nontouching_updm_expreval] >> simp[] >>
      metis_tac[upd_memory_diamond_NONE_preserved]) >>
  qmatch_assum_rename_tac `A1U gm = SOME m1` >>
  Cases_on `A2U gm` >> simp[]
  >- (fs[Abbr`A1U`, Abbr`A2U`] >>
      `MAP (lookupRW m1) a2.reads = MAP (lookupRW gm) a2.reads`
        by metis_tac[nontouching_updm_expreval, touches_SYM] >> simp[] >>
      metis_tac[upd_memory_diamond_NONE_preserved]) >>
  qmatch_assum_rename_tac `A2U gm = SOME m2` >>
  fs[Abbr`A1U`, Abbr`A2U`] >>
  `MAP (lookupRW m1) a2.reads = MAP (lookupRW gm) a2.reads ∧
   MAP (lookupRW m2) a1.reads = MAP (lookupRW gm) a1.reads`
     by metis_tac[nontouching_updm_expreval, touches_SYM] >> simp[] >>
  `w1 ≠ w2`
    by (strip_tac >> fs[touches_def] >> metis_tac[]) >>
  qabbrev_tac `d1 = a1.data (MAP (lookupRW gm) a1.reads)` >>
  qabbrev_tac `d2 = a2.data (MAP (lookupRW gm) a2.reads)` >>
  `∃m. upd_memory w1 d1 m2 = SOME m ∧ upd_memory w2 d2 m1 = SOME m`
    by metis_tac[successful_upd_memory_diamond] >>
  simp[])

val expr_reads_def = tDefine "expr_reads" `
  (expr_reads m (MAccess ma) =
     case ma_reads m ma of
         (SOME x, xs) => x::xs
       | (NONE, xs) => xs) ∧
  (expr_reads m (Opn f elist) = FLAT (MAP (expr_reads m) elist)) ∧
  (expr_reads m (Value v) = []) ∧

  (ma_reads m (ASub a i_e) =
     case (ma_reads m a, evalexpr m i_e, expr_reads m i_e) of
         ((SOME (nm, is), aux), Int i, rds) =>
           if 0 ≤ i then (SOME (nm, is ++ [Num i]), aux ++ rds)
           else (NONE, aux ++ rds)
       | ((_, aux), _, rds) => (NONE, aux ++ rds)) ∧
  (ma_reads m (VRead nm) = (SOME (nm, []), []))
` (WF_REL_TAC `measure (λs. case s of INL (_,e) => expr_size e
                                    | INR (_,m) => maccess_size m)` >> simp[] >>
   Induct >> simp[expr_size_def] >> rpt strip_tac >> simp[] >>
   res_tac >> simp[])

val readAction_def = Define`
  readAction i m e = <|
    reads := expr_reads m e;
    write := NONE;
    data := ARB : value list -> value;
    ident := i |>
`;

val readAction_ident = store_thm(
  "readAction_ident[simp]",
  ``(readAction i m e).ident = i``,
  simp[readAction_def]);

val domreadAction_def = Define`
  domreadAction i m (D lo hi) = <|
    reads := expr_reads m lo ++ expr_reads m hi;
    write := NONE;
    data := ARB : value list -> value;
    ident := i
  |> `;

val domreadAction_ident = store_thm(
  "domreadAction_ident[simp]",
  ``(domreadAction i m d).ident = i``,
  Cases_on `d` >> simp[domreadAction_def]);

val domreadAction_write = store_thm(
  "domreadAction_write[simp]",
  ``(domreadAction l m d).write = NONE``,
  Cases_on `d` >> simp[domreadAction_def]);

val dvread_def = Define`
  (dvread m (DMA ma) =
     (case ma_reads m ma of (SOME x,xs) => x::xs | (NONE, xs) => xs)) ∧
  (dvread m (DValue _) = [])
`;

val dvreadAction_def = Define`
  dvreadAction i m ds = <| reads := FLAT (MAP (dvread m) ds);
                           write := NONE;
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
  ``∀P Q. (∀v. P (Value v)) ∧
          (∀f l. (∀e. MEM e l ⇒ P e) ⇒ P (Opn f l)) ∧
          (∀ma. Q ma ⇒ P (MAccess ma)) ∧
          (∀s. Q (VRead s)) ∧
          (∀am ie. Q am ∧ P ie ⇒ Q (ASub am ie))
        ⇒
          (∀e. P e) ∧ (∀m. Q m)``,
  rpt gen_tac >> strip_tac >>
  `(!e. P e) ∧ (∀m. Q m) ∧ (∀l e. MEM e l ⇒ P e)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:expr``) >> dsimp[]);

val UNCURRY_case = prove(
  ``UNCURRY f p = pair_CASE p f``,
  Cases_on `p` >> simp[]);

(* memory access ≤ :  mv1 < mv2 if mv1 is higher in tree position than mv2 *)
val mav_le_def = Define`
  mav_le (s1:string, is1:num list) (s2, is2) ⇔ s1 = s2 ∧ is1 ≼ is2
`;
val _ = overload_on("<=", ``mav_le``)

val mav_le_TRANS = store_thm(
  "mav_le_TRANS",
  ``mav_le x y ∧ mav_le y z ⇒ mav_le x z``,
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >> simp[mav_le_def] >>
  metis_tac[IS_PREFIX_TRANS]);

val mav_le_add_index = store_thm(
  "mav_le_add_index",
  ``(s, is) ≤ (s, is ++ [v])``,
  simp[mav_le_def]);

val _ = overload_on("≰", ``λv1 v2. ¬mav_le v1 v2``)
val _ = set_fixity "≰" (Infix(NONASSOC, 450))

val upd_nested_EQ_SOME_E = store_thm(
  "upd_nested_EQ_SOME_E",
  ``upd_nested_array i is v vl0 = SOME vl ⇒
    LENGTH vl = LENGTH vl0 ∧ i < LENGTH vl0``,
  Cases_on `is` >> simp[option_case_eq, value_case_eq, PULL_EXISTS] >>
  rw[] >> rw[]);

val upd_nested_APPEND = store_thm(
  "upd_nested_APPEND",
  ``∀is i sfx v vl0 vl.
      upd_nested_array i (is ++ sfx) v vl0 = SOME vl ∧ sfx ≠ [] ⇒
      ∃svl0 svl.
        lookup_indices (EL i vl0) is = Array svl0 ∧
        upd_nested_array (HD sfx) (TL sfx) v svl0 = SOME svl ∧
        lookup_indices (EL i vl) is = Array svl``,
  Induct >> simp[]
  >- (Induct_on `sfx` >>
      simp[option_case_eq, value_case_eq, PULL_EXISTS, EL_LUPDATE]) >>
  simp[option_case_eq, value_case_eq, PULL_EXISTS, bool_case_eq,
       EL_LUPDATE] >> rpt strip_tac >>
  imp_res_tac upd_nested_EQ_SOME_E >> simp[]);

val upd_memory_APPEND = store_thm(
  "upd_memory_APPEND",
  ``∀pfx sfx v m0 m.
      sfx ≠ [] ∧ upd_memory (nm, pfx ++ sfx) v m0 = SOME m ⇒
      ∃vl0 vl.
        lookup_indices (evalmaccess m0 (VRead nm)) pfx = Array vl0 ∧
        upd_nested_array (HD sfx) (TL sfx) v vl0 = SOME vl ∧
        lookup_indices (evalmaccess m (VRead nm)) pfx = Array vl``,
  gen_tac >> `pfx = [] ∨ ∃i is. pfx = i::is` by (Cases_on `pfx` >> simp[])
  >- (simp[evalexpr_def] >> Cases_on `sfx` >>
      simp[upd_memory_def, FLOOKUP_DEF, option_case_eq,
           value_case_eq, PULL_EXISTS, lookup_v_def]) >>
  simp[evalexpr_def, upd_memory_def, FLOOKUP_DEF, option_case_eq,
       value_case_eq, PULL_EXISTS, lookup_v_def, bool_case_eq] >>
  rpt strip_tac >> imp_res_tac upd_nested_EQ_SOME_E >> simp[] >>
  metis_tac[upd_nested_APPEND]);

val lookup_indices_SNOC_Error = store_thm(
  "lookup_indices_SNOC_Error",
  ``∀is i v. ¬isArray (lookup_indices v is) ⇒
             lookup_indices v (is ++ [i]) = Error``,
  Induct >> Cases_on `v` >> simp[] >> rw[]);

val lookup_indices_APPEND = store_thm(
  "lookup_indices_APPEND",
  ``∀pfx sfx v. lookup_indices v (pfx ++ sfx) =
                lookup_indices (lookup_indices v pfx) sfx``,
  Induct_on `pfx` >> simp[] >> Cases_on `v` >> simp[] >> rw[]);

val ma_reads_evalmaccess_SOME = save_thm(
  "ma_reads_evalmaccess_SOME",
  prove(``(∀e:expr. T) ∧
    ∀ma mnm mis maux m.
      ma_reads m ma = (SOME (mnm, mis), maux) ⇒
      evalmaccess m ma = lookup_indices (evalmaccess m (VRead mnm)) mis``,
  ho_match_mp_tac expr_ind' >> simp[expr_reads_def, evalexpr_def] >>
  simp[value_case_eq, PULL_EXISTS, option_case_eq, pair_case_eq,
       bool_case_eq] >>
  rpt strip_tac >> res_tac >> csimp[lookup_indices_SNOC_Error] >>
  Cases_on `lookup_indices (lookup_v m mnm) is` >> simp[]
  >- (disj1_tac >> simp[lookup_indices_APPEND] >>
      asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) [] >>
      `i = &Num i` by metis_tac[integerTheory.INT_OF_NUM] >>
      pop_assum SUBST1_TAC >> simp[] >> rw[] >> lfs[]) >>
  simp[lookup_indices_SNOC_Error]) |> CONJUNCT2);

val aec_lemma = prove(
  ``(∀e.
       (∀rv. MEM rv (expr_reads m0 e) ⇒ rv ≰ w ∧ w ≰ rv) ∧
       upd_memory w d m0 = SOME m ⇒
       evalexpr m e = evalexpr m0 e ∧ expr_reads m e = expr_reads m0 e) ∧
    (∀ma mlvopt mrds.
       upd_memory w d m0 = SOME m ∧ ma_reads m0 ma = (mlvopt, mrds) ∧
       (∀rv. MEM rv mrds ⇒ rv ≰ w ∧ w ≰ rv) ⇒
       ma_reads m ma = ma_reads m0 ma ∧
       (mlvopt = NONE ⇒ evalmaccess m ma = Error ∧ evalmaccess m0 ma = Error) ∧
       (∀mlv. mlvopt = SOME mlv ∧ mlv ≰ w ∧ w ≰ mlv ⇒
              evalmaccess m ma = evalmaccess m0 ma))``,
  ho_match_mp_tac expr_ind' >> simp[expr_reads_def, evalexpr_def] >>
  rpt strip_tac
  >- (`MAP (evalexpr m) l = MAP (evalexpr m0) l` suffices_by simp[] >>
      simp[MAP_EQ_f] >> fs[MEM_FLAT, MEM_MAP] >> metis_tac[])
  >- (`MAP (expr_reads m) l = MAP (expr_reads m0) l` suffices_by simp[] >>
      simp[MAP_EQ_f] >> fs[MEM_FLAT, MEM_MAP] >> metis_tac[])
  >- (`∃mrds. ma_reads m0 ma = (NONE, mrds) ∨ ∃mlv. ma_reads m0 ma = (SOME mlv,mrds)`
        by metis_tac[option_CASES, pair_CASES] >> fs[])
  >- (`∃mrds. ma_reads m0 ma = (NONE, mrds) ∨ ∃mlv. ma_reads m0 ma = (SOME mlv,mrds)`
        by metis_tac[option_CASES, pair_CASES] >> fs[])
  >- (`∃ws wis. w = (ws, wis)` by (Cases_on `w` >> simp[]) >>
      fs[mav_le_def] >>
      `wis = [] ∨ ∃wh wt. wis = wh::wt` by metis_tac[list_CASES] >> veq >>
      fs[upd_memory_def, upd_var_def, lookup_v_def, option_case_eq,
         value_case_eq] >> veq >>
      simp[FLOOKUP_UPDATE] >> csimp[FLOOKUP_DEF])
  >- (`∃maux. ma_reads m0 ma = (NONE, maux) ∨ ∃mlv. ma_reads m0 ma = (SOME mlv,maux)`
        by metis_tac[option_CASES, pair_CASES] >> fs[]
      >- (`mlvopt = NONE ∧ mrds = maux ++ expr_reads m0 e`
             by (Cases_on `evalexpr m0 e` >> fs[]) >> veq >>
          fs[DISJ_IMP_THM, FORALL_AND_THM]) >>
      reverse (Cases_on `∃i. evalexpr m0 e = Int i`)
      >- (fs[value_case_eq] >> veq >> fs[DISJ_IMP_THM, FORALL_AND_THM]) >>
      pop_assum strip_assume_tac >> fs[] >>
      `mrds = maux ++ expr_reads m0 e` by fs[pair_case_eq, bool_case_eq] >>
      veq >> fs[])
  >- (`∃maux. ma_reads m0 ma = (NONE, maux) ∨ ∃mlv. ma_reads m0 ma = (SOME mlv,maux)`
        by metis_tac[option_CASES, pair_CASES] >> fs[]
      >- (`mrds = maux ++ expr_reads m0 e`
             by (Cases_on `evalexpr m0 e` >> fs[]) >> veq >>
          fs[DISJ_IMP_THM, FORALL_AND_THM]) >>
      `mrds = maux ++ expr_reads m0 e`
        by fs[value_case_eq, pair_case_eq, bool_case_eq] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      reverse (Cases_on `∃i. evalexpr m0 e = Int i`)
      >- (fs[value_case_eq] >> veq >> Cases_on `evalmaccess m ma` >> simp[]) >>
      pop_assum strip_assume_tac >> fs[pair_case_eq, bool_case_eq] >>
      asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) [] >>
      Cases_on `evalmaccess m ma` >> simp[])
  >- (veq >> fs[] >>
      `∃maux. ma_reads m0 ma = (NONE, maux) ∨ ∃mlv. ma_reads m0 ma = (SOME mlv,maux)`
        by metis_tac[option_CASES, pair_CASES] >> fs[]
      >- (`mrds = maux ++ expr_reads m0 e`
             by (Cases_on `evalexpr m0 e` >> fs[]) >> veq >>
          fs[DISJ_IMP_THM, FORALL_AND_THM]) >>
      `mrds = maux ++ expr_reads m0 e`
        by fs[value_case_eq, pair_case_eq, bool_case_eq] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      reverse (Cases_on `∃i. evalexpr m0 e = Int i`)
      >- (fs[value_case_eq] >> veq >> Cases_on `evalmaccess m0 ma` >> simp[]) >>
      pop_assum strip_assume_tac >> fs[pair_case_eq, bool_case_eq] >>
      asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) [] >>
      Cases_on `evalmaccess m0 ma` >> simp[])
  >- (veq >>
      RULE_ASSUM_TAC (SIMP_RULE (srw_ss())
                                [pair_case_eq, value_case_eq, option_case_eq,
                                 PULL_EXISTS, bool_case_eq]) >>
      fs[] >> veq >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `w ≰ (nm, is)`
        by (strip_tac >>
            `(nm, is) ≤ (nm, is ++ [Num i])` by simp[mav_le_add_index] >>
            metis_tac[mav_le_TRANS]) >> fs[] >>
      reverse (Cases_on `(nm,is) ≤ w`) >> fs[] >>
      `∃wnm wis. w = (wnm, wis)` by (Cases_on `w` >> simp[]) >> veq >>
      fs[mav_le_def] >> veq >>
      `∃sfx. wis = is ++ sfx` by metis_tac[IS_PREFIX_APPEND] >> veq >>
      fs[] >>
      `evalmaccess m0 ma = lookup_indices (evalmaccess m0 (VRead nm)) is ∧
       evalmaccess m ma = lookup_indices (evalmaccess m (VRead nm)) is`
        by metis_tac[ma_reads_evalmaccess_SOME] >>
      `sfx ≠ []` by (strip_tac >> fs[]) >>
      `∃vl0 vl.
         lookup_indices (evalmaccess m0 (VRead nm)) is = Array vl0 ∧
         lookup_indices (evalmaccess m (VRead nm)) is = Array vl ∧
         upd_nested_array (HD sfx) (TL sfx) d vl0 = SOME vl`
        by metis_tac[upd_memory_APPEND] >>
      simp[] >> asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) [] >>
      `i = &Num i` by metis_tac[integerTheory.INT_OF_NUM] >>
      pop_assum SUBST1_TAC >> simp[] >>
      imp_res_tac upd_nested_array_preserves_array_length >> simp[] >> rw[] >>
      `HD sfx ≠ Num i` by (strip_tac >> Cases_on `sfx` >> fs[]) >>
      metis_tac[upd_nested_array_EL]));

val upd_nested_valid_lookup = store_thm(
  "upd_nested_valid_lookup",
  ``∀is i vl0 vl.
      upd_nested_array i is v vl0 = SOME vl ⇒
      valid_vallookup (EL i vl0) is ∧ valid_vallookup (EL i vl) is``,
  Induct >> simp[value_case_eq, option_case_eq, PULL_EXISTS, EL_LUPDATE]
  >- (Cases_on `v` >> dsimp[EL_LUPDATE]) >>
  metis_tac[upd_nested_EQ_SOME_E]);

val upd_memory_valid_lvalue = store_thm(
  "upd_memory_valid_lvalue",
  ``upd_memory lv v m0 = SOME m ⇒ lv ∈ valid_lvalue m0 ∧ lv ∈ valid_lvalue m``,
  simp[valid_lvalue_def] >>
  `∃wnm. lv = (wnm, []) ∨ ∃wi wis. lv = (wnm, wi::wis)`
    by metis_tac[list_CASES, pair_CASES] >>
  simp[upd_memory_def, upd_var_def, option_case_eq, value_case_eq,
       FLOOKUP_DEF] >> rpt strip_tac >> simp[] >> veq >> fs[] >>
  metis_tac[upd_nested_valid_lookup, upd_nested_EQ_SOME_E]);

val evalmaccess_SOME_ma_reads = save_thm(
  "evalmaccess_SOME_ma_reads",
  prove(``(!e:expr. T) ∧
    ∀ma. evalmaccess m ma ≠ Error ⇒ ∃mnm mis maux. ma_reads m ma = (SOME(mnm, mis), maux)``,
  ho_match_mp_tac expr_ind' >>
  simp[expr_reads_def, evalexpr_def, pair_case_eq, value_case_eq, bool_case_eq,
       option_case_eq, PULL_EXISTS] >> rpt strip_tac >>
  Cases_on `evalmaccess m ma` >> fs[] >>
  Cases_on `evalexpr m e` >> fs[] >> fs[] >>
  asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) []) |> CONJUNCT2);

val valid_vallookup_APPEND = store_thm(
  "valid_vallookup_APPEND",
  ``∀pfx sfx v.
      valid_vallookup v (pfx ++ sfx) ⇔
        if valid_vallookup v pfx then sfx = []
        else
          lookup_indices v pfx ≠ Error ∧
          valid_vallookup (lookup_indices v pfx) sfx``,
  Induct >> simp[] >> Cases_on `v` >> csimp[] >>
  simp[bool_case_eq] >> qx_gen_tac `h` >> Cases_on `h < LENGTH l` >> simp[] >>
  Cases_on `valid_vallookup (EL h l) pfx` >> simp[]);

val evalma_Array_not_valid_lookup = save_thm(
  "evalma_Array_not_valid_lookup",
  prove(``(∀e:expr. T) ∧
    ∀ma mnm mis maux l.
      evalmaccess m ma = Array l ∧ ma_reads m ma = (SOME (mnm,mis), maux) ⇒
      mnm ∈ FDOM m ∧ ¬valid_vallookup (m ' mnm) mis ∧ isArray (m ' mnm) ∧
      lookup_indices (m ' mnm) mis = Array l``,
  ho_match_mp_tac expr_ind' >>
  simp[evalexpr_def, expr_reads_def, lookup_v_def, FLOOKUP_DEF, option_case_eq] >>
  rpt strip_tac >>
  fs[value_case_eq, pair_case_eq, option_case_eq, bool_case_eq]
  >- (veq >> fs[] >> veq >> fs[] >> pop_assum mp_tac >>
      simp[valid_vallookup_APPEND])
  >- (veq >> fs[lookup_indices_APPEND, bool_case_eq] >> veq >>
      Q.UNDISCH_THEN `¬(&LENGTH vlist ≤ i)` mp_tac >>
      `i = &Num i` by metis_tac[integerTheory.INT_OF_NUM] >>
      pop_assum SUBST1_TAC >> simp[])) |> CONJUNCT2)

val nonArray_evalexpr = store_thm(
  "nonArray_evalexpr",
  ``(∀e m lv. ¬isArrayError (evalexpr m e) ∧ MEM lv (expr_reads m e) ⇒
              lv ∈ valid_lvalue m) ∧
    (∀ma m. evalmaccess m ma ≠ Error ⇒
            (∀lv. MEM lv (SND (ma_reads m ma)) ⇒ lv ∈ valid_lvalue m) ∧
            (¬isArray (evalmaccess m ma) ⇒
             ∀lv. FST (ma_reads m ma) = SOME lv ⇒ lv ∈ valid_lvalue m))``,
  ho_match_mp_tac expr_ind' >> simp[expr_reads_def, evalexpr_def] >> rpt strip_tac
  >- (fs[MEM_FLAT, MEM_MAP, bool_case_eq, PULL_EXISTS, EXISTS_MEM] >>
      full_simp_tac (srw_ss() ++ COND_elim_ss) [] >>
      metis_tac[isArrayError_DISJ_EQ])
  >- (`∃maux. ma_reads m ma = (NONE, maux) ∨ ∃mlv. ma_reads m ma = (SOME mlv, maux)`
        by metis_tac[pair_CASES, option_CASES] >> fs[isArrayError_DISJ_EQ])
  >- (fs[valid_lvalue_def, lookup_v_def, FLOOKUP_DEF, option_case_eq] >> fs[] >>
      pop_assum mp_tac >> simp[] >> fs[])
  >- (Cases_on `evalmaccess m ma` >> fs[] >>
      Cases_on `evalexpr m e` >> fs[bool_case_eq] >> fs[] >>
      `∃mnm mis maux. ma_reads m ma = (SOME(mnm,mis), maux)`
         by (match_mp_tac evalmaccess_SOME_ma_reads >> simp[]) >>
      fs[] >> `0 ≤ i` by asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) [] >>
      fs[])
  >- (Cases_on `evalmaccess m ma` >> fs[] >>
      Cases_on `evalexpr m e` >> fs[bool_case_eq] >> fs[] >>
      `∃mnm mis maux. ma_reads m ma = (SOME(mnm,mis), maux)`
         by (match_mp_tac evalmaccess_SOME_ma_reads >> simp[]) >>
      fs[] >> `0 ≤ i` by asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) [] >>
      Q.UNDISCH_THEN `¬(i < 0)` assume_tac >> fs[] >> veq >>
      Q.UNDISCH_THEN `¬(&LENGTH l ≤ i)` assume_tac >> fs[] >>
      simp[valid_lvalue_def, valid_vallookup_APPEND] >>
      imp_res_tac evalma_Array_not_valid_lookup >> simp[] >>
      Q.UNDISCH_THEN `¬(&LENGTH l ≤ i)` mp_tac >>
      `i = &Num i` by metis_tac[integerTheory.INT_OF_NUM] >>
      pop_assum SUBST1_TAC >> simp[]))

val valid_lookup_incomparable = store_thm(
  "valid_lookup_incomparable",
  ``∀is1 is2 v.
      valid_vallookup v is1 ∧ valid_vallookup v is2 ∧ is1 ≠ is2 ⇒
      ¬(is1 <<= is2) ∧ ¬(is2 <<= is1)``,
  Induct >> simp[valid_vallookup_def]
  >- (Cases_on `v` >> simp[]) >>
  Cases_on `v` >> simp[PULL_EXISTS] >> metis_tac[]);

val valid_lvalues_incomparable = store_thm(
  "valid_lvalues_incomparable",
  ``∀lv1 lv2.
      lv1 ∈ valid_lvalue m ∧ lv2 ∈ valid_lvalue m ∧ lv1 ≠ lv2 ⇒
      lv1 ≰ lv2 ∧ lv2 ≰ lv1``,
  simp[valid_lvalue_def, PULL_EXISTS, mav_le_def] >>
  metis_tac[valid_lookup_incomparable]);


val apply_action_expr_eval_commutes = store_thm(
  "apply_action_expr_eval_commutes",
  ``∀a e j m0 m.
       readAction j m0 e ≁ₜ a ∧ apply_action a (SOME m0) = SOME m ∧
       ¬isArrayError (evalexpr m0 e)
     ⇒
       evalexpr m e = evalexpr m0 e ∧ readAction j m e = readAction j m0 e``,
  simp[readAction_def, touches_def, apply_action_def] >> gen_tac >>
  `a.write = NONE ∨ ∃w. a.write = SOME w` by (Cases_on `a.write` >> simp[]) >>
  simp[] >>
  REWRITE_TAC [DECIDE ``p \/ q <=> ~p ==> q``] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, MEM_FILTER] >>
  pop_assum kall_tac >> map_every qx_gen_tac [`e`, `m0`, `m`] >> strip_tac >>
  qabbrev_tac `d = a.data (MAP (lookupRW m0) a.reads)` >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  match_mp_tac (aec_lemma |> CONJUNCT1) >> simp[] >>
  qx_gen_tac `r` >> strip_tac >> `r ≠ w` by (strip_tac >> fs[]) >>
  `w ∈ valid_lvalue m0` by metis_tac [upd_memory_valid_lvalue] >>
  `r ∈ valid_lvalue m0` by metis_tac [nonArray_evalexpr] >>
  metis_tac[valid_lvalues_incomparable])

val _ = export_theory();
