open HolKernel Parse boolLib bossLib;

open lcsymtacs

open bagTheory
open PseudoCTheory
open actionGraphTheory

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
  lfs[pairTheory.LEX_DEF, pred_setTheory.MAX_SET_THM]
  >- (Cases_on `b` >> simp[])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (simp[listTheory.SUM_APPEND] >> Cases_on `expr` >> fs[isValue_def])
  >- simp[listTheory.SUM_APPEND]
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

val gtouches_def = Define`
  gtouches g1 g2 <=> ∃a1 a2. a1 ∈ g1 ∧ a2 ∈ g2 ∧ touches a1 a2
`;

open monadsyntax
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = overload_on ("assert", ``OPTION_GUARD``)

(* opt_sequence : (α option) list -> α list option *)
val OPT_SEQUENCE_def = Define`
  (OPT_SEQUENCE [] = SOME []) ∧
  (OPT_SEQUENCE (NONE :: _) = NONE) ∧
  (OPT_SEQUENCE (SOME x :: rest) = OPTION_MAP (CONS x) (OPT_SEQUENCE rest))
`;

val MEM_FOLDR_mlt = store_thm(
  "MEM_FOLDR_mlt",
  ``MEM e l ==>
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

val getReads_def = Define`
  (getReads m [] = SOME []) ∧
  (getReads m (Read vname i_e :: des) =
     lift2 (λi rest. (vname,i) :: rest)
           (some i. evalexpr m i_e = Int i)
           (getReads m des))
`;

val mergeReads0_def = Define`
  (mergeReads0 m [] acc opn vs = opn (REVERSE acc)) ∧
  (mergeReads0 m (Convert e :: ds) acc opn vs =
     mergeReads0 m ds (evalexpr m e :: acc) opn vs) ∧
  (mergeReads0 m (DValue v :: ds) acc opn vs =
     mergeReads0 m ds (v :: acc) opn vs) ∧
  (mergeReads0 m (Read _ _ :: ds) acc opn vs =
     mergeReads0 m ds (HD vs :: acc) opn (TL vs))
`;

val mergeReads_def = Define`
  mergeReads m ds opn = mergeReads0 m ds [] opn
`;

val evalDexpr_def = Define`
  (evalDexpr m (Convert e) = SOME (evalexpr m e)) ∧
  (evalDexpr m (DValue v) = SOME v) ∧
  (evalDexpr m (Read aname e_i) =
     do
       i <- (some i. evalexpr m e_i = Int i);
       SOME (lookup_array m aname i)
     od)
`;

val stackInc_def = Define`
  (stackInc [] = []) ∧
  (stackInc (h::t) = h + 1n :: t)
`;

val ap3_def = Define`
  ap3 f (x,y,z) = (x,y,f z)
`;

val graphOf_def = tDefine "graphOf" `

  (graphOf i lm m G0 (IfStmt g t e) =
     case evalexpr (lm ⊌ m) g of
       | Bool T => graphOf i lm m G0 t
       | Bool F => graphOf i lm m G0 e
       | _ => NONE) ∧

  (graphOf i lm0 m0 G0 (ForLoop vnm d body) =
     do
       dvs <- dvalues (lm0 ⊌ m0) d;
       graphOf i lm0 m0 G0 (Seq (MAP (λv. (FEMPTY |+ (vnm,v),body)) dvs))
     od) ∧

  (graphOf i lm0 m0 G0 (Seq cmds) =
     case cmds of
       | [] => SOME (lm0, m0, G0)
       | (lm,c) :: rest =>
         do
           (lm', m', G') <- graphOf i (lm ⊌ lm0) m0 G0 c;
           graphOf (stackInc i) lm0 m' G' (Seq rest)
         od) ∧

  (graphOf i lm0 m0 G0 (ParLoop vnm d body) =
     do
       dvs <- dvalues (lm0 ⊌ m0) d;
       graphOf i lm0 m0 G0 (Par (MAP (λv. (FEMPTY |+ (vnm,v), body)) dvs))
     od) ∧

  (graphOf i lm0 m0 G0 (Par cmds) =
     do
       ps0 <- OPT_SEQUENCE (MAP (λ(lm,c). graphOf i (lm ⊌ lm0) m0 G0 c) cmds);
       ps <- SOME (GENLIST (λn. ap3 (pushG n) (EL n ps0)) (LENGTH ps0));
       assert(∀i j. i < j ∧ j < LENGTH ps ⇒
                    ¬gtouches (SND (SND (EL i ps))) (SND (SND (EL j ps))));
       SOME(lm0, (@m. ∃lm. eval (lm0, m0, Par cmds) (lm, m, Done)),
            FOLDR (λ(lm,m,G) aG. merge_graph aG G) (pushG (LENGTH ps0) G0) ps)
     od) ∧

  (graphOf iter lm0 m0 G0 (Assign w ds opn) =
     do (aname,i_e) <- SOME w;
        i <- (some i. evalexpr (lm0 ⊌ m0) i_e = Int i);
        rds <- getReads (lm0 ⊌ m0) ds;
        a <- SOME <| write := (aname,i);
                     reads := rds;
                     expr := mergeReads (lm0 ⊌ m0) ds opn;
                     iter := iter |> ;
        rvs <- OPT_SEQUENCE (MAP (evalDexpr (lm0 ⊌ m0)) ds);
        m' <- upd_array m0 aname i (opn rvs);
        SOME(lm0, m', add_postaction a G0)
     od)

` (WF_REL_TAC
     `inv_image (mlt (<) LEX (<)) (λ(i,lm,m,g,s). (loopbag s, stmt_weight s))` >>
   simp[WF_mlt1, rich_listTheory.FOLDR_MAP, mlt_loopbag_lemma] >>
   rpt strip_tac
   >- (imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `SND` mp_tac) >>
       rw[] >> simp[] >> pop_assum kall_tac >> pop_assum mp_tac >>
       map_every qid_spec_tac [`lm`, `c`] >> Induct_on `cmds` >> dsimp[] >>
       rpt strip_tac >> res_tac >> decide_tac))


val _ = export_theory();
