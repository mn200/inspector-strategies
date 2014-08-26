open HolKernel Parse boolLib bossLib;

open lcsymtacs
open actionTheory actionGraphTheory
open PseudoCTheory PseudoCPropsTheory
open bagTheory pairTheory pred_setTheory listTheory rich_listTheory
open indexedListsTheory
open finite_mapTheory
open intLib

open monadsyntax boolSimps

val _ = new_theory "naiveGraph";

fun disjneq_search (g as (asl,w)) = let
  val ds = strip_disj w
  fun is_neq t = is_eq (dest_neg t) handle HOL_ERR _ => false
in
  case List.find is_neq ds of
      NONE => NO_TAC
    | SOME d => ASM_CASES_TAC (dest_neg d) THEN ASM_REWRITE_TAC[]
end g

val commutes_lemma = prove(
  ``∀a1 a2 s.
      ¬(a1 ∼ₜ a2) ∧ a1.ident ≠ a2.ident ⇒
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

val stackInc_def = Define`stackInc = updLast SUC`
val _ = temp_overload_on ("isuc", ``stackInc``)

val stackInc_11 = store_thm(
  "stackInc_11[simp]",
  ``isuc x = isuc y ⇔ x = y``,
  simp[stackInc_def] >>
  rw[updLast_FRONT_LAST] >>
  metis_tac[APPEND_FRONT_LAST]);

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
        a <- SOME <| writes := [Array aname i];
                     reads := rds;
                     data := mergeReads ds opn;
                     ident := stackInc (stackInc i0) |> ;
        rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
        m' <- upd_array m0 aname i (opn rvs);
        SOME(stackInc (stackInc (stackInc i0)), m', a0 ⊕ (a1 ⊕ (a ⊕ emptyG)))
     od) ∧

  (graphOf i0 m0 (AssignVar vnm ds opn) =
     do
       rds <- getReads m0 ds;
       a0 <- SOME(dvreadAction i0 m0 ds);
       a <- SOME <| writes := [Variable vnm];
                    reads := rds;
                    data := mergeReads ds opn;
                    ident := stackInc i0 |> ;
       rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
       m' <- updf (Variable vnm) (opn rvs) m0;
       SOME(stackInc (stackInc i0), m', a0 ⊕ (a ⊕ emptyG))
     od) ∧

  (graphOf i0 m0 Abort = NONE) ∧

  (graphOf i0 m0 Done = SOME(i0,m0,emptyG)) ∧

  (graphOf i0 m0 (Malloc vnm sz value) = NONE) ∧

  (graphOf i0 m0 (Label v s) = graphOf i0 m0 s)
` (WF_REL_TAC
     `inv_image (mlt (<) LEX (<)) (λ(i,m,s). (loopbag s, stmt_weight (K 0) (K 0) s))` >>
   simp[WF_mlt1, FOLDR_MAP, mlt_loopbag_lemma] >>
   rpt strip_tac >> TRY (rw[mlt_loopbag_lemma, MAX_PLUS] >> NO_TAC)
   >- (imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `I` mp_tac) >>
       rw[] >> simp[] >> qpat_assum `MEM c cmds` mp_tac >>
       rpt (pop_assum kall_tac) >>
       qid_spec_tac `c` >> Induct_on `cmds` >> dsimp[] >>
       rpt strip_tac >> res_tac >> decide_tac))

val eval_ind' = save_thm(
  "eval_ind'",
  PseudoCTheory.eval_strongind
    |> SIMP_RULE (srw_ss()) [FORALL_PROD]
    |> Q.SPEC `\a1 a2. P (FST a1) (SND a1) (FST a2) (SND a2)`
    |> SIMP_RULE (srw_ss()) []);

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

val idents_FOLDR_merge_graph = store_thm(
  "idents_FOLDR_merge_graph",
  ``i ∈ idents (FOLDR merge_graph g0 glist) ⇔
    i ∈ idents g0 ∨ ∃g. MEM g glist ∧ i ∈ idents g``,
  Induct_on `glist` >> simp[] >> metis_tac[]);

val SNOC_11 = prove(
  ``INJ (λi. i ++ [x]) s UNIV``,
  simp[INJ_IFF]);

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

val graphOf_idents_apart = store_thm(
  "graphOf_idents_apart",
  ``∀i0 m0 c i m g.
       graphOf i0 m0 c = SOME(i,m,g) ∧ i0 ≠ [] ⇒
       i0 ≤ i ∧ LENGTH i = LENGTH i0 ∧ FRONT i = FRONT i0 ∧
       ∀j. j ∈ idents g ⇒ i0 ≤ j ∧ j < i ∧
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
      simp[Once graphOf_def, PULL_EXISTS, idents_FOLDR_merge_graph,
           PULL_EXISTS, ilistLT_stackInc,
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
      simp[Once graphOf_def, FRONT_TAKE, PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      `∀x. x ≠ [] ⇒ x < isuc x ∧ x < isuc (isuc x)`
        by metis_tac[ilistLT_stackInc, ilistLT_trans, stackInc_EQ_NIL] >>
      dsimp[] >> conj_tac >- metis_tac[ilistLE_LTEQ] >>
      metis_tac[FRONT_stackInc, FRONT_TAKE, LENGTH_stackInc,
                stackInc_EQ_NIL])
  >- ((* Abort *) simp[Once graphOf_def])
  >- ((* Done *) simp[Once graphOf_def])
  >- ((* Malloc *) simp[graphOf_def])
  >- ((* Label *) simp[graphOf_def])
);

val pcg_eval_merge_graph = store_thm(
  "pcg_eval_merge_graph",
  ``(∀a. a ∈ g1 ⇒ a.ident ∉ idents g2) ⇒
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

val assign_lemma = store_thm(
  "assign_lemma",
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
  Cases_on `i ∈ idents g` >> simp[pcg_eval_thm, add_action_id'] >>
  simp[readAction_def, apply_action_def]);

val pcg_eval_domreadAction = store_thm(
  "pcg_eval_domreadAction[simp]",
  ``pcg_eval (domreadAction i m d ⊕ g) mo = pcg_eval g mo``,
  Cases_on `i ∈ idents g` >> simp[pcg_eval_thm, add_action_id'] >>
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
      `i0 ≤ i' ∧ (∀j. j ∈ idents g1 ⇒ j < i') ∧ i' ≠ [] ∧
       (∀j. j ∈ idents g2 ⇒ i' ≤ j)`
         by metis_tac[graphOf_idents_apart, ilistLE_NIL] >>
      `∀a. a ∈ g1 ⇒ a.ident ∉ idents g2`
        by (fs[idents_thm, PULL_EXISTS] >>
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
      simp[graphOf_def, pcg_eval_thm, updf_def, apply_action_def, PULL_EXISTS,
           mergeReads_def] >> metis_tac[assign_lemma, REVERSE_DEF, APPEND])
  >- ((* Abort *) simp[graphOf_def])
  >- ((* Done *) simp[graphOf_def, pcg_eval_thm])
  >- ((* Malloc *) simp[graphOf_def])
  >- ((* Label *) simp[graphOf_def])
);

val assert_EQ_SOME = store_thm(
  "assert_EQ_SOME[simp]",
  ``(assert b = SOME x) <=> b``,
  Cases_on `b` THEN SIMP_TAC (srw_ss()) [oneTheory.one]);

val INJ_UNION_DOMAIN = store_thm(
  "INJ_UNION_DOMAIN",
  ``INJ f (p ∪ q) r ⇔
      INJ f p r ∧ INJ f q r ∧
      DISJOINT (IMAGE f (p DIFF q)) (IMAGE f (q DIFF p))``,
  dsimp[INJ_IFF, EQ_IMP_THM] >> rw[]
  >- (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]));

val imap_merge_graph = store_thm(
  "imap_merge_graph",
  ``INJ f (idents g1 ∪ idents g2) UNIV ∧
    DISJOINT (idents g1) (idents g2) ⇒
    imap f (merge_graph g1 g2) = merge_graph (imap f g1) (imap f g2)``,
  map_every qid_spec_tac [`g1`, `g2`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm] >> rpt strip_tac >>
  fs[INSERT_UNION_EQ, ONCE_REWRITE_RULE [UNION_COMM] INSERT_UNION_EQ] >>
  `DISJOINT (idents g1) (idents g2) ∧
   DISJOINT (a.ident INSERT idents g1) (idents g2)`
    by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `INJ f (a.ident INSERT idents g1) UNIV ∧
   INJ f (a.ident INSERT idents g2) UNIV ∧
   INJ f (idents g1) UNIV ∧ INJ f (idents g2) UNIV`
    by (fs[INJ_UNION_DOMAIN, INJ_INSERT] >> fs[INJ_IFF] >>
        metis_tac[]) >>
  `∀j. j ∈ idents g1 ∨ j ∈ idents g2 ⇒ (f a.ident ≠ f j)`
    by (rpt strip_tac >> fs[INJ_INSERT, DISJOINT_DEF, EXTENSION] >>
        metis_tac[]) >>
  csimp[imap_add_action, merge_graph_thm, idents_imap,
        imap_add_postaction, INSERT_UNION_EQ,
        ONCE_REWRITE_RULE [UNION_COMM] INSERT_UNION_EQ]);

val INJ_CONG = store_thm(
  "INJ_CONG",
  ``(∀x. x ∈ s ⇒ f x = g x) ⇒ (INJ f s t ⇔ INJ g s t)``,
  simp[INJ_IFF]);

val match_imp = let
  fun f th = SUBGOAL_THEN (lhand (concl th)) (mp_tac o MATCH_MP th)
in
  disch_then f
end

val imap_FOLDRi_merge = store_thm(
  "imap_FOLDRi_merge",
  ``∀f g.
      (∀i j. i < j ∧ j < LENGTH l ⇒
        DISJOINT (idents (g i (EL i l)))
                 (idents (g j (EL j l)))) ∧
      (∀i. i < LENGTH l ⇒
           DISJOINT (idents (g i (EL i l))) (idents G)) ∧
      INJ f (idents G ∪
             idents (FOLDRi (λn c. merge_graph (g n c)) G l))
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
        dsimp[Abbr`AG`, idents_FOLDRi_merge] >>
        metis_tac[DISJOINT_SYM]) >>
  simp[combinTheory.o_DEF]);

val graphOf_starting_id_irrelevant = store_thm(
  "graphOf_starting_id_irrelevant",
  ``∀i0 m0 c0 i m g.
       graphOf i0 m0 c0 = SOME (i, m, g) ∧ i0 ≠ [] ⇒
       ∀i0'.
        i0' ≠ [] ⇒
        ∃f.
          graphOf i0' m0 c0 = SOME(f i, m, imap f g) ∧
          i0' = f i0 ∧ INJ f (i INSERT idents g) UNIV``,
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
      `stackInc i0 ≤ i ∧ ∀j. j ∈ idents g ⇒ stackInc i0 ≤ j`
        by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
      `i0 < stackInc i0` by metis_tac[ilistLT_stackInc] >>
      `i0 < i ∧ i0 ≠ i` by metis_tac[ilistLE_REFL, ilistLTE_trans] >>
      `i0 ∉ idents g` by metis_tac[ilistLTE_trans, ilistLE_REFL] >>
      `ff i0 = i0' ∧ ff i = f i` by simp[Abbr`ff`] >> simp[] >>
      `∀j. j ∈ idents g ⇒ ff j = f j` by (simp[Abbr`ff`] >> metis_tac[]) >>
      `INJ ff (i0 INSERT idents g) UNIV`
        by (simp[INJ_INSERT] >> simp[Cong INJ_CONG] >>
            asm_simp_tac (srw_ss() ++ CONJ_ss ++ ETA_ss) [] >>
            fs[INJ_INSERT] >> qx_gen_tac `y` >> strip_tac >>
            `f y ∈ idents (imap f g)` by simp[idents_imap] >>
            `stackInc i0' ≤ f y`
              by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
            `i0' < stackInc i0'` by metis_tac[ilistLT_stackInc] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_add_action] >> simp[Cong imap_CONG] >>
      simp[readAction_def] >> simp[Once INJ_INSERT] >>
      asm_simp_tac (srw_ss() ++ CONJ_ss ++ DNF_ss) [] >>
      qx_gen_tac `y` >> fs[INJ_INSERT] >> Cases_on `y = i0` >> simp[] >>
      `stackInc i0' ≤ f i`
        by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
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
      `(∀k. k ∈ idents g ⇒ stackInc i0 ≤ k ∧ i0 < k) ∧ stackInc i0 ≤ i ∧
       i0 < i`
        by metis_tac[graphOf_idents_apart, ilistLTE_trans, ilistLE_REFL]>>
      `i0 ∉ idents g ∧ i0 ≠ i` by metis_tac[ilistLE_REFL] >>
      `ff i0 = j ∧ ff i = f i` by simp[Abbr`ff`] >>
      `∀k. k ∈ idents g ⇒ ff k = f k` by (simp[Abbr`ff`] >> metis_tac[]) >>
      simp[] >>
      `INJ ff (i0 INSERT idents g) UNIV`
        by (fs[INJ_INSERT, Cong INJ_CONG] >> csimp[] >> qx_gen_tac `y` >>
            strip_tac >> full_simp_tac (srw_ss() ++ ETA_ss) [] >>
            `f y ∈ idents (imap f g)` by simp[idents_imap] >>
            `stackInc (f y) ≤ f y`
              by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
            metis_tac[ilistLT_stackInc, stackInc_EQ_NIL,
                      ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_add_action] >> simp[Cong imap_CONG] >>
      Cases_on `d` >> simp[domreadAction_def] >> simp[Once INJ_INSERT] >>
      dsimp[] >> csimp[] >> fs[INJ_INSERT] >>
      `stackInc j ≤ f i`
        by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
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
            INJ f1 (i0' INSERT idents g1) UNIV`
        by metis_tac[] >> simp[] >>
      Q.UNDISCH_THEN `graphOf i0 m0 h = SOME(i0',m0',g1)`
        (fn th => first_x_assum
                    (fn impth => mp_tac (MATCH_MP impth th) >>
                                 assume_tac th)) >>
      simp[] >>
      first_x_assum (kall_tac o assert(is_forall o concl)) >>
      `i0' ≠ [] ∧ i0 ≤ i0' ∧ i0' ≤ i ∧ (∀k. k ∈ idents g1 ⇒ k < i0') ∧
       ∀k. k ∈ idents g2 ⇒ i0' ≤ k`
        by metis_tac[graphOf_idents_apart, ilistLE_NIL] >>
      simp[] >>
      `DISJOINT (idents g1) (idents g2)`
        by (simp[DISJOINT_DEF, EXTENSION] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      disch_then (qspec_then `f1 i0'` mp_tac) >> simp[] >>
      `f1 i0' ≠ [] ∧ (∀k. k ∈ idents (imap f1 g1) ⇒ k < f1 i0')`
        by metis_tac[graphOf_idents_apart, ilistLE_NIL] >>
      simp[] >> disch_then (qx_choose_then `f2` strip_assume_tac) >>
      simp[] >>
      `∀k. k ∈ idents (imap f2 g2) ⇒ f1 i0' ≤ k`
        by metis_tac[graphOf_idents_apart] >>
      `INJ f1 (idents g1) UNIV ∧ INJ f2 (idents g2) UNIV`
        by fs[INJ_INSERT] >>
      qabbrev_tac `
        ff = λk. if k ∈ idents g2 ∨ k = i then f2 k else f1 k` >>
      qexists_tac `ff` >>
      `f2 i = ff i` by simp[Abbr`ff`] >> simp[] >>
      `f1 i0 = ff i0`
        by (rw[Abbr`ff`] >> metis_tac[ilistLE_antisym]) >> simp[] >>
      `i ∉ idents g1` by metis_tac[ilistLTE_trans, ilistLE_REFL] >>
      `(∀k. k ∈ idents g1 ⇒ ff k = f1 k) ∧
       (∀k. k ∈ idents g2 ⇒ ff k = f2 k)`
        by (simp[Abbr`ff`] >> qx_gen_tac `k` >> strip_tac >>
            `k ∉ idents g2 ∧ k ≠ i`
              by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
            simp[]) >>
      `INJ ff (idents g1 ∪ idents g2) UNIV`
        by (simp[INJ_UNION_DOMAIN] >>
            `INJ ff (idents g1) UNIV ∧ INJ ff (idents g2) UNIV`
              by full_simp_tac (srw_ss() ++ ETA_ss)
                   [Cong INJ_CONG] >>
            `idents g1 DIFF idents g2 = idents g1 ∧
             idents g2 DIFF idents g1 = idents g2`
              by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
            simp[Cong (REWRITE_RULE [GSYM AND_IMP_INTRO] IMAGE_CONG)] >>
            CONV_TAC (DEPTH_CONV ETA_CONV) >>
            fs[idents_imap, PULL_EXISTS] >>
            simp[DISJOINT_DEF, EXTENSION] >>
            metis_tac[ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_merge_graph, Cong imap_CONG] >>
      simp[INJ_INSERT] >> dsimp[] >> reverse conj_tac
      >- (`∀k. k ∈ idents (imap f2 g2) ⇒ k < ff i`
            by metis_tac[graphOf_idents_apart] >> pop_assum mp_tac >>
          dsimp[idents_imap] >> csimp[] >> metis_tac[ilistLE_REFL]) >>
      csimp[] >>
      `f2 i0' ≤ f2 i` by metis_tac[graphOf_idents_apart] >>
      fs[idents_imap, PULL_EXISTS] >>
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
      `(∀k. k ∈ idents g ⇒ stackInc i0 ≤ k ∧ i0 < k) ∧ stackInc i0 ≤ i ∧
       i0 < i`
        by metis_tac[graphOf_idents_apart, ilistLTE_trans, ilistLE_REFL]>>
      `i0 ∉ idents g ∧ i0 ≠ i` by metis_tac[ilistLE_REFL] >>
      `ff i0 = j ∧ ff i = f i` by simp[Abbr`ff`] >>
      `∀k. k ∈ idents g ⇒ ff k = f k` by (simp[Abbr`ff`] >> metis_tac[]) >>
      simp[] >>
      `INJ ff (i0 INSERT idents g) UNIV`
        by (fs[INJ_INSERT, Cong INJ_CONG] >> csimp[] >> qx_gen_tac `y` >>
            strip_tac >> full_simp_tac (srw_ss() ++ ETA_ss) [] >>
            `f y ∈ idents (imap f g)` by simp[idents_imap] >>
            `stackInc (f y) ≤ f y`
              by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
            metis_tac[ilistLT_stackInc, stackInc_EQ_NIL,
                      ilistLTE_trans, ilistLE_REFL]) >>
      simp[imap_add_action] >> simp[Cong imap_CONG] >>
      Cases_on `d` >> simp[domreadAction_def] >> simp[Once INJ_INSERT] >>
      dsimp[] >> csimp[] >> fs[INJ_INSERT] >>
      `stackInc j ≤ f i`
        by metis_tac[graphOf_idents_apart, stackInc_EQ_NIL] >>
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
      `∀n. n < LENGTH cs ⇒ INJ (ff n) (idents (gfg n)) UNIV`
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
      `∀n j. n < LENGTH cs ∧ j ∈ idents (imap (ff n) (gfg n)) ⇒
             i0' ++ [n;0] ≤ j ∧
             TAKE (LENGTH (i0' ++ [n;0]) - 1) j = FRONT (i0' ++ [n;0])`
        by (rpt gen_tac >> strip_tac >> res_tac >>
            `i0' ++ [n;0] ≠ []` by simp[] >>
            metis_tac[graphOf_idents_apart]) >>
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
                qx_gen_tac `it` >> Cases_on `it ∈ idents (gfg i)` >>
                simp[] >>
                `i < LENGTH cs` by decide_tac >> strip_tac >>
                `TAKE (LENGTH (i0 ++ [i;0]) - 1) it = i0 ++ [i] ∧
                 TAKE (LENGTH (i0 ++ [j;0]) - 1) it = i0 ++ [j]`
                  by metis_tac[graphOf_idents_apart] >>
                fs[]) >>
            dsimp[idents_FOLDRi_merge, INJ_IFF] >>
            map_every qx_gen_tac [`it1`, `it2`, `i`, `j`] >> strip_tac >>
            `TAKE (LENGTH (i0 ++ [i;0]) - 1) it1 = i0 ++ [i] ∧
             TAKE (LENGTH (i0 ++ [j;0]) - 1) it2 = i0 ++ [j] ∧
             LENGTH (i0 ++ [i;0]) ≤ LENGTH it1 ∧
             LENGTH (i0 ++ [j;0]) ≤ LENGTH it2`
                by metis_tac[graphOf_idents_apart] >>
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
                `ff i it1 ∈ idents (imap (ff i) (gfg i)) ∧
                 ff j it2 ∈ idents (imap (ff j) (gfg j))`
                  by simp[idents_imap] >>
                `∀i. i < LENGTH cs ⇒ ff i (i0 ++ [i; 0]) ≠ []`
                  by metis_tac[APPEND_eq_NIL, NOT_CONS_NIL] >>
                `TAKE (LENGTH (i0' ++ [i;0]) - 1) (ff i it1) =
                 FRONT (i0' ++ [i;0]) ∧
                 TAKE (LENGTH (i0' ++ [j;0]) - 1) (ff j it2) =
                 FRONT (i0' ++ [j;0])`
                  by metis_tac[graphOf_idents_apart] >>
                fs[FRONT_APPEND] >>
                strip_tac >> fs[]) >>
            pop_assum SUBST_ALL_TAC >> fs[INJ_IFF]) >>
        `∀i. i < LENGTH cs ⇒ imap fff (gfg i) = imap (ff i) (gfg i)`
          by (pop_assum kall_tac >> simp[Abbr`fff`] >> qx_gen_tac `i` >>
              strip_tac >>
              match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] imap_CONG) >>
              simp[] >> qx_gen_tac `it` >> strip_tac >>
              `LENGTH (i0 ++ [i;0]) ≤ LENGTH it ∧
               TAKE (LENGTH (i0 ++ [i;0]) - 1) it = FRONT (i0 ++ [i;0])`
                by metis_tac[graphOf_idents_apart, APPEND_eq_NIL,
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
                         [INJ_INSERT, idents_FOLDRi_merge] >>
            `∀i n. i ∈ idents (gfg n) ∧ n < LENGTH cs ⇒
                   LENGTH (i0 ++ [n;0]) ≤ LENGTH i ∧
                   TAKE (LENGTH (i0 ++ [n;0]) - 1) i = FRONT (i0 ++ [n;0])`
              by metis_tac[APPEND_eq_NIL, NOT_CONS_NIL,
                           graphOf_idents_apart] >>
            `∀i n. i ∈ idents (gfg n) ∧ n < LENGTH cs ⇒
                   EL (LENGTH i0) i = n`
              by (rpt strip_tac >> lfs[FRONT_APPEND] >> res_tac >>
                  `EL (LENGTH i0) i =
                   EL (LENGTH i0) (TAKE (LENGTH i0 + 1) i)`
                    by simp[EL_TAKE] >> simp[EL_APPEND2]) >>
            reverse conj_tac
            >- (map_every qx_gen_tac [`y`, `n`] >> strip_tac >>
                qpat_assum `y ∈ idents (gfg n)`
                  (fn i => qpat_assum `n < LENGTH cs`
                  (fn l => rpt (first_x_assum
                                  (strip_assume_tac o
                                   C MATCH_MP (CONJ i l))) >>
                           assume_tac i >> assume_tac l)) >>
                qpat_assum `fff (stackInc i0) = fff y` mp_tac >>
                simp[Abbr`fff`] >> lfs[FRONT_APPEND] >>
                `y ≠ i0 ∧ y ≠ stackInc i0` by (rpt strip_tac >> lfs[]) >>
                simp[] >>
                `ff n y ∈ idents (imap (ff n) (gfg n))`
                  by simp[idents_imap] >>
                `LENGTH (i0' ++ [n; 0]) ≤ LENGTH (ff n y)`
                  by metis_tac[graphOf_idents_apart, NOT_CONS_NIL,
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
            `ff i it1 ∈ idents (imap (ff i) (gfg i)) ∧
             ff j it2 ∈ idents (imap (ff j) (gfg j))`
              by simp[idents_imap] >>
            qpat_assum `imap fff ggg = XXX` kall_tac >>
            qpat_assum `∀i. i < LENGTH cs ⇒ imap fff ggg = g'g'g'` kall_tac >>
            `TAKE (LENGTH (i0' ++ [i;0]) - 1) (ff i it1) = FRONT (i0' ++ [i;0]) ∧
             TAKE (LENGTH (i0' ++ [j;0]) - 1) (ff j it2) = FRONT (i0' ++ [j;0])`
              by metis_tac[graphOf_idents_apart, NOT_CONS_NIL,
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
            imap_add_action] >>
      rpt gen_tac >> strip_tac >> qx_gen_tac `j0` >> strip_tac >>
      qexists_tac `
        λi. if i = i0 then j0 else if i = stackInc i0 then stackInc j0
            else isuc (isuc j0)` >> simp[] >> conj_tac
      >- simp[dvreadAction_def] >>
      qx_gen_tac `k` >> rpt strip_tac >> rw[] >>
      pop_assum mp_tac >> simp[])
  >- ((* Abort *) simp[graphOf_def])
  >- ((* Done *) csimp[graphOf_def, INJ_INSERT] >> strip_tac >>
      qx_gen_tac `j0` >> strip_tac >> qexists_tac `K j0` >> simp[])
  >- ((* Malloc *) simp[graphOf_def])
  >- ((* Label *) simp[graphOf_def])
);

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

val isDValue_destDValue = store_thm(
  "isDValue_destDValue",
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

val pcg_eval_NONE = store_thm(
  "pcg_eval_NONE[simp]",
  ``∀g. pcg_eval g NONE = NONE``,
  ho_match_mp_tac graph_ind >> simp[pcg_eval_thm, apply_action_def] >>
  rpt gen_tac >> Cases_on `a.writes` >> simp[]);

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
  `a1.writes = [] ∨ ∃w1 t1. a1.writes = w1::t1`
    by (Cases_on `a1.writes` >> simp[]) >>
  `a2.writes = [] ∨ ∃w2 t2. a2.writes = w2::t2`
    by (Cases_on `a2.writes` >> simp[]) >> simp[apply_action_def]
  >- (rw[] >> simp[]) >> strip_tac >> simp[] >> rw[] >>
  `MAP (lookupRW m2) a1.reads = MAP (lookupRW m0) a1.reads ∧
   MAP (lookupRW m1) a2.reads = MAP (lookupRW m0) a2.reads`
    by metis_tac[nontouching_updfs_expreval, touches_SYM] >>
  simp[] >>
  qmatch_rename_tac
    `∃m. updf w1 v1 m2 = SOME m ∧ updf w2 v2 m1 = SOME m` [] >>
  fs[touches_def] >> `w1 ≠ w2` by metis_tac[MEM] >>
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

val mkWFA_def = Define`
  mkWFA a =
    case a.writes of
        [] => a
      | h::t => <| reads := a.reads ;
                   writes := [h] ;
                   data := a.data;
                   ident := a.ident |>
`;

val touches_mkWFA = store_thm(
  "touches_mkWFA",
  ``mkWFA a ∼ₜ b ⇒ a ∼ₜ b``,
  simp[touches_def, mkWFA_def] >> Cases_on `a.writes` >> simp[] >>
  metis_tac[]);

val apply_action_mkWFA = store_thm(
  "apply_action_mkWFA[simp]",
  ``apply_action (mkWFA a) m_opt = apply_action a m_opt``,
  simp[apply_action_def, mkWFA_def] >> Cases_on `m_opt` >> simp[] >>
  Cases_on `a.writes` >> simp[]);

val apply_action_dvreadAction_commutes = store_thm(
  "apply_action_dvreadAction_commutes",
  ``a ≁ₜ dvreadAction i m0 ds ∧ apply_action a (SOME m0) = SOME m ∧
    getReads m0 ds = SOME rds ∧
    (a.writes ≠ [] ⇒ ¬MEM (HD a.writes) rds)
   ⇒
    dvreadAction i m ds = dvreadAction i m0 ds ∧
    getReads m ds = getReads m0 ds ∧
    MAP (evalDexpr m) ds = MAP (evalDexpr m0) ds``,
  simp[dvreadAction_def, touches_def, MEM_FLAT, MEM_MAP, PULL_FORALL,
       GSYM IMP_DISJ_THM] >>
  `a.writes = [] ∨ ∃w t. a.writes = w::t` by (Cases_on `a.writes` >> simp[]) >>
  simp[FORALL_AND_THM, GSYM LEFT_FORALL_OR_THM, PULL_EXISTS,
       GSYM RIGHT_FORALL_OR_THM] >- csimp[apply_action_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `apply_action a (SOME m0) = SOME m` >> simp[] >>
  `apply_action (mkWFA a) (SOME m0) = SOME m` by simp[] >>
  `(mkWFA a).writes = [w]` by simp[mkWFA_def] >> qabbrev_tac `b = mkWFA a` >>
  Q.RM_ABBREV_TAC `b` >> ntac 2 (pop_assum mp_tac) >>
  rpt (pop_assum kall_tac) >> ntac 2 strip_tac >> strip_tac >>
  first_x_assum
    (kall_tac o assert (equal 2 o length o #1 o strip_forall o concl)) >>
  ntac 3 (pop_assum mp_tac) >>
  qid_spec_tac `rds` >> Induct_on `ds` >>
  simp[getReads_def] >> Cases >> simp[getReads_def, dvread_def, evalDexpr_def]
  >- (simp[dvread_def, DISJ_IMP_THM, FORALL_AND_THM] >> ntac 4 strip_tac >>
      `readAction i m0 e ≁ₜ b` by (simp[readAction_def, touches_def]) >>
      `readAction i m e = readAction i m0 e ∧ evalexpr m e = evalexpr m0 e`
        by metis_tac[apply_action_expr_eval_commutes] >>
      fs[readAction_def] >> BasicProvers.VAR_EQ_TAC >> fs[] >>
      qmatch_assum_rename_tac `w ≠ Array anm i : actionRW` [] >>
      imp_res_tac some_EQ_SOME_E >> fs[] >>
      `evalexpr m0 (ARead anm e) = lookup_array m0 anm i ∧
       evalexpr m (ARead anm e) = lookup_array m anm i`
        by simp[evalexpr_def] >>
      `b ≁ₜ readAction jj m0 (ARead anm e)`
        by simp[readAction_def, touches_def, expr_reads_def] >>
      metis_tac[apply_action_expr_eval_commutes, touches_SYM]) >>
  simp[dvread_def, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
  simp[PULL_FORALL] >> qx_gen_tac `z` >> rpt strip_tac >>
  qmatch_assum_rename_tac `w ≠ Variable v` [] >>
  `evalexpr m0 (VRead v) = lookup_v m0 v ∧
   evalexpr m (VRead v) = lookup_v m v`
    by simp[evalexpr_def] >>
  `b ≁ₜ readAction jj m0 (VRead v)`
    by simp[touches_def, readAction_def, expr_reads_def] >>
  metis_tac[apply_action_expr_eval_commutes, touches_SYM])

val _ = temp_type_abbrev(
  "tosty",
  ``:(num list # memory #
      (value list -> value, actionRW, num list)action_graph) option``)

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
      `i0 ∉ idents g'`
        by metis_tac[ilistLT_stackInc, ilistLTE_trans,
                     stackInc_EQ_NIL, ilistLE_REFL, graphOf_idents_apart] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `evalexpr m2 gd = evalexpr m0 gd ∧
       readAction i0 m2 gd = readAction i0 m0 gd`
        by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
      simp[EXISTS_PROD] >> metis_tac[])
  >- (map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      ONCE_REWRITE_TAC [graphOf_def] >> simp[PULL_EXISTS, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `dvs`, `g`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `i0 ∉ idents g`
        by metis_tac[ilistLT_stackInc, ilistLTE_trans,
                     stackInc_EQ_NIL, ilistLE_REFL, graphOf_idents_apart] >>
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
      `i1 ≠ []` by metis_tac[graphOf_idents_apart, LENGTH_NIL] >>
      `∀b. b ∈ g2 ⇒ b.ident ∉ idents g1`
        by (gen_tac >> strip_tac >>
            `b.ident ∈ idents g2` by simp[idents_thm] >>
            metis_tac[graphOf_idents_apart, ilistLTE_trans, ilistLE_REFL])>>
      full_simp_tac (srw_ss() ++ CONJ_ss) [] >>
      metis_tac[])
  >- ((* parloop *)
      map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      ONCE_REWRITE_TAC [graphOf_def] >> simp[PULL_EXISTS, EXISTS_PROD] >>
      map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `dvs`, `g`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `i0 ∉ idents g`
        by metis_tac[ilistLT_stackInc, ilistLTE_trans,
                     stackInc_EQ_NIL, ilistLE_REFL, graphOf_idents_apart] >>
      `dvalues m2 d = dvalues m0 d ∧
       domreadAction i0 m2 d = domreadAction i0 m0 d`
        by metis_tac[apply_action_dvalues_commutes] >>
      simp[] >> metis_tac[])
  >- ((* par *)
      qx_gen_tac `cmds` >> strip_tac >> map_every qx_gen_tac [`i`, `m1`, `m2`, `a`, `g`] >>
      ONCE_REWRITE_TAC [graphOf_def] >>
      simp[OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R, MEM_MAPi, PULL_EXISTS] >>
      qabbrev_tac `TOS = λt:tosty. THE (OPTION_MAP (SND o SND) t)` >> simp[] >>
      simp[FOLDR_MAPi, combinTheory.o_ABS_R] >> fs[] >> strip_tac >> fs[] >>
      csimp[] >>
      `∃m. pcg_eval g (SOME m2) = SOME m ∧ apply_action a (SOME m1) = SOME m`
        by metis_tac[pcg_eval_apply_action_diamond] >> simp[] >>
      qabbrev_tac `GG = λi. graphOf (i0 ++ [i;0])` >> simp[] >>
      `∀it j. j < LENGTH cmds ∧ it ∈ idents (TOS (GG j m0 (EL j cmds))) ⇒
              EL (LENGTH i0) it = j`
        by (rpt strip_tac >>
            `∃j' m' g'. graphOf (i0 ++ [j;0]) m0 (EL j cmds) = SOME (j',m',g')`
              by (fs[EXISTS_PROD] >> metis_tac[]) >>
            `TOS (GG j m0 (EL j cmds)) = g'` by simp[Abbr`GG`, Abbr`TOS`] >>
            `∀k. k ∈ idents g' ⇒
                 LENGTH (i0 ++ [j;0]) ≤ LENGTH k ∧
                 TAKE (LENGTH (i0 ++ [j;0]) - 1) k = FRONT (i0 ++ [j;0])`
              by metis_tac[APPEND_eq_NIL, NOT_CONS_NIL,
                           graphOf_idents_apart] >>
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
              `ident ∈ idents (TOS (GG i m0 (EL i cmds)))` [] >>
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
      `a.writes ≠ [] ⇒ ¬MEM (HD a.writes) rds`
        by (Cases_on `a.writes` >> fs[touches_def] >> metis_tac[]) >>
      `getReads m2 ds = getReads m0 ds ∧
       dvreadAction (isuc i0) m2 ds = dvreadAction (isuc i0) m0 ds ∧
       MAP (evalDexpr m2) ds = MAP (evalDexpr m0) ds`
        by metis_tac[apply_action_dvreadAction_commutes] >> simp[] >>
      qabbrev_tac `b = <|
        reads := []; writes := [Array anm iv]; ident := xx;
        data := K (opn rvs) : value list -> value |>` >>
      `∀m. upd_array m anm iv (opn rvs) = apply_action b (SOME m)`
        by simp[apply_action_def, Abbr`b`, updf_def] >> fs[] >>
      `a ≁ₜ b` by (simp[touches_def, Abbr`b`] >> fs[touches_def] >>
                  Cases_on `a.writes` >> fs[]) >>
      metis_tac[successful_action_diamond])
  >- ((* assignvar *)
      csimp[graphOf_def, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM] >>
      map_every qx_gen_tac [`vnm`, `ds`, `opn`, `m1`, `m2`, `a`, `rds`, `rvs`] >>
      strip_tac >>
      `a.writes ≠ [] ⇒ ¬MEM (HD a.writes) rds`
        by (Cases_on `a.writes` >> fs[touches_def] >> metis_tac[]) >>
      `dvreadAction i0 m2 ds = dvreadAction i0 m0 ds ∧
       getReads m2 ds = getReads m0 ds ∧
       MAP (evalDexpr m2) ds = MAP (evalDexpr m0) ds`
        by metis_tac[apply_action_dvreadAction_commutes] >> simp[] >>
      qabbrev_tac `b = <| reads := []; writes := [Variable vnm]; ident := ARB;
                          data := K(opn rvs):value list -> value |>` >>
      `∀m. updf (Variable vnm) (opn rvs) m = apply_action b (SOME m)`
        by simp[apply_action_def, Abbr`b`, updf_def] >>
      `a ≁ₜ b` by (simp[touches_def, Abbr`b`] >> fs[touches_def]) >>
      metis_tac[successful_action_diamond])
  >- ((* abort *) simp[graphOf_def])
  >- ((* Done *) simp[graphOf_def])
  >- ((* malloc *) simp[graphOf_def])
  >- ((* Label *) simp[graphOf_def])
);

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

val eval_graphOf_action = store_thm(
  "eval_graphOf_action",
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      m0 ≠ m ⇒
      ∀i0 i0' m0' g0.
        i0 ≠ [] ∧ graphOf i0 m0 c0 = SOME(i0', m0', g0) ⇒
        ∃a. a ∈ g0 ∧ (∀b. b ∈ pregraph a g0 ⇒ b.writes = []) ∧
            apply_action a (SOME m0) = SOME m``,
  ho_match_mp_tac eval_ind' >> rpt conj_tac >> REWRITE_TAC []
  >- ((* member of Seq steps *)
      map_every qx_gen_tac [`c`, `c0`, `pfx`, `sfx`, `m0`, `m`] >>
      ntac 2 strip_tac >> fs[] >> simp[Once graphOf_def] >>
      reverse (Induct_on `pfx`) >> simp[PULL_EXISTS, EXISTS_PROD]
      >- (strip_tac >> fs[] >> simp[Once graphOf_def] >> metis_tac[]) >>
      map_every qx_gen_tac [`i0`, `i`, `mm`, `i'`, `m'`, `g'`, `gg`] >>
      strip_tac >>
      `∃a. a ∈ g' ∧ (∀b. b ∈ pregraph a g' ⇒ b.writes = []) ∧
           apply_action a (SOME m0) = SOME m`
        by metis_tac[] >>
      qexists_tac `a` >> simp[pregraph_merge_graph])
  >- ((* assignvar *)
      simp[graphOf_def, PULL_EXISTS] >> rpt gen_tac >>
      rpt strip_tac >> dsimp[] >>
      conj_tac
      >- (rw[pregraph_add_action] >> simp[dvreadAction_def]) >>
      simp[apply_action_def, updf_def, mergeReads_def] >>
      fs[updf_def] >>
      imp_res_tac assign_lemma >> simp[] >>
      fs[OPT_SEQUENCE_EQ_SOME, MEM_MAP, PULL_EXISTS] >> rw[] >>
      imp_res_tac isDValue_destDValue >> fs[])
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
        TOS = λt:tosty.
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
             DISJOINT (idents (gg i)) (idents (gg j))`
        by (map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
            first_x_assum (fn th =>
              map_every (fn q => qspec_then q mp_tac th) [`i`, `j`]) >>
            simp[Abbr`GG`] >> rpt strip_tac >>
            `(∀it. it ∈ idents (gg i) ⇒
                   TAKE (LENGTH (i0 ++ [i;0]) - 1) it = FRONT (i0 ++ [i;0])) ∧
             (∀it. it ∈ idents (gg j) ⇒
                   TAKE (LENGTH (i0 ++ [j;0]) - 1) it = FRONT (i0 ++ [j;0]))`
              by metis_tac[graphOf_idents_apart, APPEND_eq_NIL] >>
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
        pregraph_FOLDRi_merge_graph >> simp[])
  >- ((* malloc *) simp[graphOf_def])
  >- ((* Label *) simp[graphOf_def] >> metis_tac[])
);

val _ = temp_overload_on ("MergeL", ``FOLDR merge_graph emptyG``)

val FOLDR_merge_lemma = prove(
  ``(∀g. MEM g l1 ⇒ ¬gtouches g e ∧ DISJOINT (idents g) (idents e)) ⇒
    FOLDR merge_graph emptyG (l1 ++ [e] ++ l2) =
    merge_graph e (FOLDR merge_graph emptyG (l1 ++ l2))``,
  Induct_on `l1` >> dsimp[merge_graph_ASSOC] >>
  metis_tac[nontouching_merge_COMM])

val pcg_eval_merge_graph' = prove(
  ``DISJOINT (idents g1) (idents g2) ⇒
    pcg_eval (merge_graph g1 g2) = pcg_eval g2 o pcg_eval g1``,
  simp[FUN_EQ_THM] >> rpt strip_tac >>
  match_mp_tac pcg_eval_merge_graph >>
  fs[DISJOINT_DEF, EXTENSION, idents_thm] >>
  metis_tac[]);

val idents_MergeL = prove(
  ``idents (MergeL l) = BIGUNION (IMAGE idents (set l))``,
  dsimp[Once EXTENSION, idents_FOLDR_merge_graph] >>
  metis_tac[]);

val MergeL_empty = prove(
  ``MergeL (l1 ++ [emptyG] ++ l2) = MergeL (l1 ++ l2)``,
  Induct_on `l1` >> simp[]);

val MergeL_append = prove(
  ``MergeL (l1 ++ l2) = merge_graph (MergeL l1) (MergeL l2)``,
  Induct_on `l1` >> simp[merge_graph_ASSOC])

val imap_MergeL = prove(
  ``(∀g. MEM g glist ⇒ INJ f (idents g) UNIV) ∧
    (∀i j. i < j ∧ j < LENGTH glist ⇒
           DISJOINT (idents (EL i glist)) (idents (EL j glist)) ∧
           DISJOINT (IMAGE f (idents (EL i glist)))
                    (IMAGE f (idents (EL j glist))))
    ⇒
     imap f (MergeL glist) = MergeL (MAP (λg. imap f g) glist)``,
  Induct_on `glist` >> simp[] >> dsimp[LT_SUC] >> qx_gen_tac `h` >>
  strip_tac >> fs[] >>
  `INJ f (idents h ∪ idents (MergeL glist)) UNIV`
    by (simp[INJ_UNION_DOMAIN, idents_MergeL] >>
        dsimp[INJ_DEF] >> conj_tac
        >- (map_every qx_gen_tac [`it1`, `it2`, `g1`, `g2`] >> strip_tac >>
            Cases_on `g1 = g2` >- metis_tac [INJ_DEF] >>
            `(∃i. i < LENGTH glist ∧ g1 = EL i glist) ∧
             ∃j. j < LENGTH glist ∧ g2 = EL j glist` by metis_tac[MEM_EL] >>
            `i ≠ j` by (strip_tac >> fs[]) >>
            fs[DISJOINT_DEF, EXTENSION] >>
            `i < j ∨ j < i` by decide_tac >> metis_tac[]) >>
        `idents h DIFF BIGUNION (IMAGE idents (set glist)) =
         idents h`
          by (simp[Once EXTENSION] >> qx_gen_tac `it` >> eq_tac >> simp[] >>
              strip_tac >> qx_gen_tac `s` >> Cases_on `it ∈ s` >> simp[] >>
              qx_gen_tac `g` >> disjneq_search >> BasicProvers.VAR_EQ_TAC >>
              fs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_EL]) >>
        `BIGUNION (IMAGE idents (set glist)) DIFF idents h =
         BIGUNION (IMAGE idents (set glist))`
          by (simp[Once EXTENSION] >> dsimp[] >> qx_gen_tac `it` >>
              eq_tac >> strip_tac >- metis_tac[] >>
              fs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_EL]) >>
        simp[] >> simp[DISJOINT_DEF, Once EXTENSION] >>
        simp[GSYM IMP_DISJ_THM, PULL_FORALL] >>
        qx_gen_tac `it` >>
        ONCE_REWRITE_TAC [DECIDE ``p \/ q ⇔ ¬p ⇒ q``] >>
        simp[PULL_EXISTS] >> qx_gen_tac `it0` >> strip_tac >>
        BasicProvers.VAR_EQ_TAC >> map_every qx_gen_tac [`it'`, `g`] >>
        rpt strip_tac >>
        `g ≠ h` by (strip_tac >> fs[DISJOINT_DEF, EXTENSION] >>
                    metis_tac[MEM_EL]) >>
        fs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_EL]) >>
  `DISJOINT (idents h) (idents (MergeL glist))`
    by (simp[idents_MergeL, DISJOINT_DEF, Once EXTENSION] >>
        simp[GSYM IMP_DISJ_THM, PULL_FORALL] >>
        fs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_EL]) >>
  simp[imap_merge_graph]);

val MergeL_empties = store_thm(
  "MergeL_empties",
  ``(∀g. MEM g glist ⇒ g = emptyG) ⇒ MergeL glist = emptyG``,
  Induct_on `glist` >> simp[]);

val MAPi_MAP_o = store_thm(
  "MAPi_MAP_o",
  ``∀l f g. MAPi f (MAP g l) = MAPi (λn. f n o g) l``,
  Induct_on `l` >> simp[combinTheory.o_ABS_L]);


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
      map_every qx_gen_tac [`c`, `c0`] >> reverse Induct >> simp[]
      >- (ONCE_REWRITE_TAC [graphOf_def] >>
          simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
          first_assum MATCH_ACCEPT_TAC) >>
      ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      rpt strip_tac >>
      qmatch_assum_rename_tac `graphOf i0 m0 c0 = SOME(i00,m00,g00)` [] >>
      `∃i' g'. graphOf i0 m c = SOME(i',m00,g') ∧
               ∀g''. gtouches g' g'' ⇒ gtouches g00 g''`
         by metis_tac[] >> simp[] >>
      qmatch_assum_rename_tac `
        graphOf i00 m00 (Seq rest) = SOME(i0',m0',rg)` []>>
      `i00 ≠ [] ∧ i' ≠ []` by metis_tac[graphOf_idents_apart, LENGTH_NIL] >>
      `∃f. graphOf i' m00 (Seq rest) = SOME(f i0',m0',imap f rg) ∧
           i' = f i00 ∧ INJ f (i0' INSERT idents rg) UNIV`
        by metis_tac[graphOf_starting_id_irrelevant] >>
      simp[] >> fs[INJ_INSERT, IN_imap] >> dsimp[] >>
      dsimp[gtouches_def] >> rpt strip_tac
      >- (fs[gtouches_def] >> metis_tac[]) >>
      disj2_tac >>
      `(∀j. j ∈ idents rg ⇒ i00 ≤ j) ∧ ∀j. j ∈ idents g00 ⇒ j < i00`
        by metis_tac[graphOf_idents_apart] >>
      `∀a. a ∈ rg ⇒ a.ident ∉ idents g00` suffices_by metis_tac[] >>
      qx_gen_tac `a` >> strip_tac >>
      `a.ident ∈ idents rg` by simp[idents_thm] >>
      metis_tac[ilistLTE_trans, ilistLE_REFL])
  >- ((* seq is all Dones *)
      qx_gen_tac `m0` >> Induct_on `cs` >> simp[] >>
      ONCE_REWRITE_TAC [graphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD] >> fs[])
  >- ((* guard of if evaluates to boolean and next statement selected *)
      map_every qx_gen_tac [`m0`, `gd`, `t`, `e`, `b`] >>
      rpt gen_tac >> strip_tac >> simp[Once graphOf_def, SimpL ``$==>``] >>
      simp[graphOf_def, SimpR ``$==>``] >>
      Cases_on `b` >> simp[EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      map_every qx_gen_tac [`i0`, `i`, `m`, `g`] >>
      strip_tac >>
      qmatch_assum_rename_tac `graphOf (stackInc i0) m0 cc = SOME (i,m,g)` []>>
      `∃f. graphOf i0 m0 cc = SOME (f i, m, imap f g) ∧
           INJ f (i INSERT idents g) UNIV ∧
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
      simp[graphOf_def, PULL_EXISTS, updf_def, OPT_SEQUENCE_EQ_SOME,
           MEM_MAP, isDValue_destDValue])
  >- ((* index of array-read in assign var is evaluated *)
      simp[graphOf_def, PULL_EXISTS, evalDexpr_def, evalexpr_def,
           OPT_SEQUENCE_EQ_SOME, MEM_MAP, getReads_APPEND,
           getReads_def] >> rpt gen_tac >>
      simp[MAP_MAP_o, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      csimp[] >> rpt strip_tac
      >- (fs[dvreadAction_def, touches_def, dvread_def,
             expr_reads_def] >> metis_tac[])
      >- (fs[touches_def] >> metis_tac[]))
  >- ((* array read in assign-var reads memory *)
      dsimp[graphOf_def, OPT_SEQUENCE_EQ_SOME, MEM_MAP, evalDexpr_def,
            evalexpr_def] >>
      dsimp[getReads_APPEND, getReads_def] >>
      simp[touches_def, dvreadAction_def, dvread_def] >>
      metis_tac[])
  >- ((* var-read inside assign-var reads memory *)
      dsimp[graphOf_def, OPT_SEQUENCE_EQ_SOME, evalDexpr_def, MEM_MAP] >>
      dsimp[getReads_def, getReads_APPEND] >>
      simp[touches_def, dvreadAction_def, dvread_def] >> metis_tac[])
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
      `∀i m f l.
         graphOf i m (Seq (MAP (λx. Label x (f x)) l)) =
         graphOf i m (Seq (MAP f l))`
        by (Induct_on `l` >> ONCE_REWRITE_TAC [graphOf_def] >>
            simp[] >> ONCE_REWRITE_TAC [graphOf_def] >> simp[]) >>
      simp[] >>
      metis_tac[stackInc_EQ_NIL, graphOf_starting_id_irrelevant,
                gtouches_imap])
  >- ((* forloop aborts because domain evaluates badly *)
      ONCE_REWRITE_TAC [graphOf_def] >> simp[])
  >- ((* parloop turns into par *)
      rpt gen_tac >> strip_tac >> simp[Once graphOf_def, SimpL ``$==>``] >>
      simp[EXISTS_PROD, PULL_EXISTS] >>
      `∀i m f l.
         graphOf i m (Par (MAP (λx. Label x (f x)) l)) =
         graphOf i m (Par (MAP f l))`
        by (simp[graphOf_def, MAPi_MAP_o, combinTheory.o_ABS_L]) >>
      simp[] >>
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
        TOS = λt:tosty.
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
                `∃a. a ∈ gg ci ∧ (∀b. b ∈ pregraph a (gg ci) ⇒ b.writes = []) ∧
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
            `∃a. a ∈ gg ci ∧ (∀b. b ∈ pregraph a (gg ci) ⇒ b.writes = []) ∧
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
           DISJOINT (idents g) (idents cg') ∧
           DISJOINT (idents g) (idents (gg ci))`
        by (simp[MEM_GENLIST, PULL_EXISTS] >> qx_gen_tac `n` >>
            strip_tac >> conj_tac
            >- (first_x_assum (qspecl_then [`n`, `ci`] mp_tac) >>
                simp[EL_APPEND2, EL_APPEND1] >>
                first_x_assum (qspec_then `n` mp_tac) >>
                simp[EL_APPEND2, EL_APPEND1]) >>
            `n < ci + (LENGTH sfx + 1)` by decide_tac >>
            pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
            simp[EL_APPEND1] >> qunabbrev_tac `GG` >> fs[] >> strip_tac >>
            `(∀it. it ∈ idents (gg n) ⇒
                   TAKE (LENGTH (i0 ++ [n;0]) - 1) it =
                   FRONT (i0 ++ [n;0])) ∧
             (∀it. it ∈ idents cg' ∨ it ∈ idents (gg ci) ⇒
                   TAKE (LENGTH (i0 ++ [ci;0]) - 1) it =
                   FRONT (i0 ++ [ci;0]))`
              by metis_tac[graphOf_idents_apart, APPEND_eq_NIL] >>
            fs[FRONT_APPEND] >> simp[DISJOINT_DEF, EXTENSION] >>
            `i0 ++ [ci] ≠ i0 ++ [n]` by simp[] >>
            metis_tac[]) >>
      fs[FOLDR_merge_lemma] >>
      conj_tac
      >- (qmatch_abbrev_tac `
            pcg_eval (merge_graph cg' RestG) (SOME m) = SOME m00
          ` >>
          `DISJOINT (idents cg') (idents RestG) ∧
           DISJOINT (idents (gg ci)) (idents RestG)`
            suffices_by (strip_tac >> fs[pcg_eval_merge_graph']) >>
          ONCE_REWRITE_TAC [DISJOINT_SYM] >>
          simp[Abbr`RestG`, idents_MergeL, PULL_EXISTS] >>
          simp[MEM_GENLIST, PULL_EXISTS, PULL_FORALL] >>
          `∀n. n < LENGTH sfx ⇒
               DISJOINT (idents (gg (ci + (n + 1))))
                        (idents cg') ∧
               DISJOINT (idents (gg (ci + (n + 1))))
                        (idents (gg ci))`
            suffices_by metis_tac[] >>
          gen_tac >> strip_tac >>
          `ci + (n + 1) < ci + (LENGTH sfx + 1)` by decide_tac >>
          pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
          simp[EL_APPEND2] >> qunabbrev_tac `GG` >> fs[] >> strip_tac >>
          `(∀it. it ∈ idents (gg (ci + (n + 1))) ⇒
                 TAKE (LENGTH (i0 ++ [ci + (n + 1);0]) - 1) it =
                 FRONT (i0 ++ [ci + (n + 1);0])) ∧
           (∀it. it ∈ idents cg' ∨ it ∈ idents (gg ci) ⇒
                 TAKE (LENGTH (i0 ++ [ci;0]) - 1) it =
                 FRONT (i0 ++ [ci;0]))`
            by metis_tac[graphOf_idents_apart, APPEND_eq_NIL] >>
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
      `a1.ident ∉ idents (gg ci)` suffices_by simp[] >>
      strip_tac >>
      `a1.ident ∈ idents BG` by simp[idents_thm] >>
      fs[idents_FOLDR_merge_graph, Abbr`BG`]
      >- (res_tac >> fs[DISJOINT_DEF, EXTENSION] >>
          metis_tac[]) >>
      qpat_assum `MEM g (GENLIST f n)` mp_tac >>
      simp[MEM_GENLIST, PULL_EXISTS] >> qx_gen_tac `n` >>
      disjneq_search >> BasicProvers.VAR_EQ_TAC >> strip_tac >>
      `ci + (n + 1) < ci + (LENGTH sfx + 1)` by decide_tac >>
      pop_assum (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
      simp[EL_APPEND2, Abbr`GG`] >> strip_tac >> fs[] >>
      `TAKE (LENGTH (i0 ++ [ci; 0]) - 1) a1.ident =
       FRONT (i0 ++ [ci;0]) ∧
       TAKE (LENGTH (i0 ++ [ci + (n + 1); 0]) - 1) a1.ident =
       FRONT (i0 ++ [ci + (n + 1);0])`
        by metis_tac[graphOf_idents_apart, APPEND_eq_NIL] >>
      fs[FRONT_APPEND])
  >- ((* par is all Dones component *)
      simp[graphOf_def, PULL_EXISTS, OPT_SEQUENCE_EQ_SOME,
           combinTheory.o_ABS_L, combinTheory.o_ABS_R,
           MEM_MAPi] >>
      map_every qx_gen_tac [`m0`, `cs`] >> strip_tac >>
      `∀n. n < LENGTH cs ⇒ EL n cs = Done` by fs[EVERY_EL] >>
      simp[MAPi_GENLIST, combinTheory.S_ABS_L] >>
      simp[Cong GENLIST_CONG] >>
      simp[MergeL_empties, MEM_GENLIST, PULL_EXISTS] >>
      simp[pcg_eval_thm])
  >- ((* Par contains an abort *)
      simp[graphOf_def, OPT_SEQUENCE_EQ_SOME, MEM_MAPi,
           PULL_EXISTS] >>
      map_every qx_gen_tac [`m0`, `cs`] >> simp[MEM_EL] >>
      disch_then (qx_choose_then `n` strip_assume_tac) >>
      `∀i m. graphOf i m Abort = NONE` by simp[] >>
      metis_tac[optionTheory.NOT_NONE_SOME])
  >- ((* Malloc *) simp[graphOf_def])
  >- ((* evaluate under a Label *) simp[graphOf_def])
  >- ((* Label-Done ---> Done *) simp[graphOf_def])
  >- ((* Label-Abort ---> Abort*) simp[graphOf_def])
);

val _ = overload_on("--->*", ``RTC eval``)
val _ = overload_on("--->⁺", ``TC eval``)
val _ = set_fixity "--->*" (Infix(NONASSOC, 450))
val _ = set_fixity "--->⁺" (Infix(NONASSOC, 450))

val graphOf_correct0 = prove(
  ``∀p1 p2.
      p1 --->* p2 ⇒
      ∀m0 c0 m i0 i g gm.
        p1 = (m0,c0) ∧ p2 = (m,Done) ∧ i0 ≠ [] ∧
        graphOf i0 m0 c0 = SOME(i,gm,g) ⇒
        gm = m``,
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >>
  simp[FORALL_PROD] >> metis_tac[graphOf_correct_lemma]);

val graphOf_correct = save_thm(
  "graphOf_correct",
  graphOf_correct0 |> SIMP_RULE (srw_ss()) [PULL_FORALL])

val _ = export_theory();
