open HolKernel Parse boolLib bossLib;

open lcsymtacs
open actionTheory hidagTheory
open PseudoCTheory PseudoCPropsTheory
open bagTheory pairTheory pred_setTheory listTheory rich_listTheory
open indexedListsTheory
open finite_mapTheory
open intLib

open monadsyntax boolSimps

val _ = new_theory "PseudoCHDAG";

fun disjneq_search (g as (asl,w)) = let
  val ds = strip_disj w
  fun is_neq t = is_eq (dest_neg t) handle HOL_ERR _ => false
in
  case List.find is_neq ds of
      NONE => NO_TAC
    | SOME d => ASM_CASES_TAC (dest_neg d) THEN ASM_REWRITE_TAC[]
end g

val FORALL_hinode = store_thm(
  "FORALL_hinode",
  ``(∀n. P n) ⇔ (∀a. P (HD a)) ∧ (∀g. P (HG g))``,
  simp[EQ_IMP_THM] >> rpt strip_tac >> Cases_on `n` >> simp[]);

fun firstn_conjs_under_exists n th = let
  val (v, body) = dest_exists (concl th)
  val body_th = ASSUME body
  val wanted_body = LIST_CONJ (List.take(CONJUNCTS body_th, n))
  val wanted = mk_exists(v, concl wanted_body)
  val ex_th0 = EXISTS(wanted, v) wanted_body
in
  CHOOSE(v,th) ex_th0
end

val gentouches_touches = store_thm(
  "gentouches_touches[simp]",
  ``gentouches (set o action_reads) (set o action_writes)
               (set o action_reads) (set o action_writes) a1 a2 ⇔
      a1 ∼ₜ a2``,
  simp[touches_def, gentouches_def]);

val gflat_eval_def = new_specification(
  "gflat_eval_def", ["gflat_eval"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:memory option -> memory option``,
                  alpha |-> ``:actionRW``,
                  beta |-> ``:α # (value list -> value)``]
    |> Q.SPECL [`λm. m`,
                `λn g nr gr m.
                    case n of
                        HD a => gr (apply_action (polydata_upd SND a) m)
                      | _ => gr m`,
                `ARB`, `ARB`,
                `K ∅`, `K ∅`, `K ∅`,`K ∅`]
    |> SIMP_RULE (srw_ss()) []
    |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [FORALL_hinode]))
    |> SIMP_RULE (srw_ss()) [apply_action_commutes]
    |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]
    |> SIMP_RULE (srw_ss()) [RIGHT_EXISTS_AND_THM]
    |> firstn_conjs_under_exists 2)

val pcg_eval_def = Define`
  pcg_eval g = gflat_eval (gflatten g)
`;

val pcn_eval_def = Define`
  pcn_eval n = gflat_eval (nflatten n)
`;

val gflat_eval_merge = store_thm(
  "gflat_eval_merge[simp]",
  ``∀m. gflat_eval (g1 ⊕ g2) m = gflat_eval g2 (gflat_eval g1 m)``,
  Induct_on `g1` >> simp[gflat_eval_def] >> gen_tac >> strip_tac >>
  Cases >> simp[]);

val pcg_eval_thm = store_thm(
  "pcg_eval_thm[simp]",
  ``(pcg_eval ε m = m) ∧
    (pcg_eval (n <+ g) m = pcg_eval g (pcn_eval n m)) ∧
    (pcn_eval (HD a) m = apply_action (polydata_upd SND a) m) ∧
    (pcn_eval (HG g) m = pcg_eval g m)``,
  simp[pcg_eval_def, pcn_eval_def, gflat_eval_def]);

val addLabel_def = Define`
  addLabel l a = polydata_upd (λv. (l,v)) a
`;

val stmt_weight_ssubst0 = store_thm(
  "stmt_weight_ssubst0[simp]",
  ``stmt_weight (K 0) (K 0) (ssubst x y s) = stmt_weight (K 0) (K 0) s``,
  qid_spec_tac `s` >> ho_match_mp_tac PseudoCTheory.stmt_induction >>
  simp[PseudoCTheory.ssubst_def, MAP_MAP_o, combinTheory.o_DEF,
       Cong (REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG)] >> rpt strip_tac >>
  Cases_on `d` >> rw[PseudoCTheory.ssubst_def])

val graphOf_def = tDefine "graphOf" `

  (graphOf lab m0 (IfStmt gd t e) =
     case evalexpr m0 gd of
       | Bool T => do
                     (m,g) <- graphOf lab m0 t;
                     SOME(m,HD (addLabel lab (readAction () m0 gd)) <+ g)
                   od
       | Bool F => do
                     (m,g) <- graphOf lab m0 e;
                     SOME(m,HD (addLabel lab (readAction () m0 gd)) <+ g)
                   od
       | _ => NONE) ∧

  (graphOf i0 m0 (ForLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       (m,g) <-
         FOLDL (λmg0 v.
                   do
                     (m0,g0) <- mg0;
                     (m,g') <- graphOf (v::lab) m0 (ssubst vnm v body);
                     SOME(m,g0 ⊕ (HG g' <+ ε))
                   od)
               (SOME(m0,ε))
               dvs;
       SOME(m, HD (addLabel i0 (domreadAction () m0 d)) <+ g)
     od) ∧

  (graphOf i0 m0 (Seq cmds) =
     FOLDL (λmg0 c.
              do
                (m0,g0) <- mg0;
                (m,g) <- graphOf i0 m0 c;
                SOME(m,g0 ⊕ (HG g <+ ε))
              od)
           (SOME(m0, ε))
           cmds) ∧

  (graphOf i0 m0 (ParLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       gs <- OPT_SEQUENCE
               (MAP (λv. OPTION_MAP
                           SND
                           (graphOf (v::i0) m0 (ssubst vnm v body)))
                    dvs);
       assert(∀i j. i < j ∧ j < LENGTH gs ⇒ ¬(EL i gs ∼ᵍ EL j gs));
       g <- SOME (FOLDR (λg acc. HG g <+ acc) ε gs);
       m <- pcg_eval g (SOME m0);
       SOME(m,HD (addLabel i0 (domreadAction () m0 d)) <+ g)
     od) ∧

  (graphOf i0 m0 (Par cmds) =
     do
       gs <-
         OPT_SEQUENCE
           (MAP (λc. OPTION_MAP SND (graphOf i0 m0 c)) cmds);
       assert(∀i j. i < j ∧ j < LENGTH gs ⇒ ¬(EL i gs ∼ᵍ EL j gs));
       g <- SOME (FOLDR (λg acc. HG g <+ acc) ε gs);
       m <- pcg_eval g (SOME m0);
       SOME(m, g)
     od) ∧

  (graphOf i0 m0 (Assign w ds opn) =
     do (aname,i_e) <- SOME w;
        i <- (some i. evalexpr m0 i_e = Int i);
        rds <- getReads m0 ds;
        a0 <- SOME (HD (addLabel i0 (readAction () m0 i_e)));
        a1 <- SOME (HD (addLabel i0 (dvreadAction () m0 ds)));
        a <- SOME (HD <| writes := [Array aname i];
                         reads := rds;
                         data := (i0, mergeReads ds opn);
                         ident := () |>) ;
        rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
        m' <- upd_array m0 aname i (opn rvs);
        SOME(m', a0 <+ a1 <+ a <+ ε)
     od) ∧

  (graphOf i0 m0 (AssignVar vnm ds opn) =
     do
       rds <- getReads m0 ds;
       a0 <- SOME(HD (addLabel i0 (dvreadAction () m0 ds)));
       a <- SOME (HD <| writes := [Variable vnm];
                        reads := rds;
                        data := (i0,mergeReads ds opn);
                        ident := () |>);
       rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
       m' <- updf (Variable vnm) (opn rvs) m0;
       SOME(m', a0 <+ a <+ ε)
     od) ∧

  (graphOf i0 m0 Abort = NONE) ∧

  (graphOf i0 m0 Done = SOME(m0,ε)) ∧

  (graphOf i0 m0 (Malloc vnm sz value) = NONE)
` (WF_REL_TAC
     `inv_image (mlt (<) LEX (<)) (λ(i,m,s). (loopbag s, stmt_weight (K 0) (K 0) s))` >>
   simp[WF_mlt1, FOLDR_MAP, mlt_loopbag_lemma] >>
   rpt strip_tac >> TRY (rw[mlt_loopbag_lemma, MAX_PLUS] >> NO_TAC)
   >- (imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `I` mp_tac) >>
       rw[] >> simp[] >> qpat_assum `MEM c cmds` mp_tac >>
       rpt (pop_assum kall_tac) >>
       qid_spec_tac `c` >> Induct_on `cmds` >> dsimp[] >>
       rpt strip_tac >> res_tac >> decide_tac)
   >- (imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `I` mp_tac) >>
       rw[] >> simp[] >> qpat_assum `MEM c cmds` mp_tac >>
       rpt (pop_assum kall_tac) >>
       qid_spec_tac `c` >> Induct_on `cmds` >> dsimp[] >>
       rpt strip_tac >> res_tac >> decide_tac)
   >- (disj1_tac >> rw[] >>
       simp[mlt_dominates_thm1] >>
       map_every qexists_tac [`BAG_IMAGE SUC (loopbag body)`, `loopbag body`] >>
       dsimp[dominates_def] >> metis_tac[DECIDE ``x < SUC x``])
   >- (disj1_tac >> rw[] >>
       simp[mlt_dominates_thm1] >>
       map_every qexists_tac [`BAG_IMAGE SUC (loopbag body)`, `loopbag body`] >>
       dsimp[dominates_def] >> metis_tac[DECIDE ``x < SUC x``])
)

val eval_ind' = save_thm(
  "eval_ind'",
  PseudoCTheory.eval_strongind
    |> SIMP_RULE (srw_ss()) [FORALL_PROD]
    |> Q.SPEC `\a1 a2. P (FST a1) (SND a1) (FST a2) (SND a2)`
    |> SIMP_RULE (srw_ss()) []);

val OPTION_IGNORE_BIND_EQUALS_OPTION = store_thm(
  "OPTION_IGNORE_BIND_EQUALS_OPTION[simp]",
  ``((OPTION_IGNORE_BIND x y = NONE) <=> (x = NONE) \/ (y = NONE)) /\
    ((OPTION_IGNORE_BIND x y = SOME z) <=>
      (?x'. x = SOME x') /\ (y = SOME z))``,
  Cases_on `x` THEN SIMP_TAC (srw_ss()) []);

val SNOC_11 = prove(
  ``INJ (λi. i ++ [x]) s UNIV``,
  simp[INJ_IFF]);

val updLast_EQ_NIL = store_thm(
  "updLast_EQ_NIL[simp]",
  ``updLast f l = [] ⇔ l = []``,
  Induct_on `l` >> simp[] >> Cases_on `l` >> simp[]);

val OPT_SEQUENCE_EQ_SOME = store_thm(
   "OPT_SEQUENCE_EQ_SOME",
   ``∀l. OPT_SEQUENCE optlist = SOME l ⇔
         (∀e. MEM e optlist ⇒ ∃v. e = SOME v) ∧
         (l = MAP THE optlist)``,
   Induct_on `optlist` >> dsimp[OPT_SEQUENCE_def] >>
   csimp[] >> metis_tac []);

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

val pcg_eval_merge_graph = store_thm(
  "pcg_eval_merge_graph",
  ``pcg_eval (g1 ⊕ g2) m_opt = pcg_eval g2 (pcg_eval g1 m_opt)``,
  map_every qid_spec_tac [`m_opt`, `g2`, `g1`] >>
  Induct >> simp[]);

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

val addLabel_readswrites = store_thm(
  "addLabel_readswrites[simp]",
  ``(addLabel l a).reads = a.reads ∧ (addLabel l a).writes = a.writes``,
  simp[addLabel_def]);

val pcg_eval_readAction = store_thm(
  "pcg_eval_readAction[simp]",
  ``pcg_eval (HD (addLabel l (readAction i m e)) <+ g) mo = pcg_eval g mo``,
  simp[pcg_eval_thm] >>
  simp[readAction_def, apply_action_def]);

val pcg_eval_domreadAction = store_thm(
  "pcg_eval_domreadAction[simp]",
  ``pcg_eval (HD (addLabel l (domreadAction i m d)) <+ g) mo = pcg_eval g mo``,
  simp[pcg_eval_thm] >>
  Cases_on `d` >> simp[domreadAction_def, apply_action_def]);

val pcg_eval_dvreadAction = store_thm(
  "pcg_eval_dvreadAction[simp]",
  ``pcg_eval (HD (addLabel l (dvreadAction i m d)) <+ g) mo = pcg_eval g mo``,
  simp[pcg_eval_thm, dvreadAction_def, apply_action_def]);

val graphOf_pcg_eval = store_thm(
  "graphOf_pcg_eval",
  ``∀i0 m0 c m g.
      graphOf i0 m0 c = SOME(m,g) ⇒ pcg_eval g (SOME m0) = SOME m``,
  ho_match_mp_tac (theorem "graphOf_ind") >> rpt conj_tac >>
  map_every qx_gen_tac [`i0`, `m0`]
  >- ((* if *)
      map_every qx_gen_tac [`gd`, `t`, `e`] >> strip_tac >>
      simp[graphOf_def] >>
      Cases_on `evalexpr m0 gd` >> simp[] >>
      fs[] >> COND_CASES_TAC >> fs[EXISTS_PROD, PULL_EXISTS])
  >- ((* forloop *)
      simp[graphOf_def, PULL_EXISTS, FORALL_PROD, FOLDL_FOLDR_REVERSE] >>
      qx_genl_tac [`vnm`, `d`, `body`] >> strip_tac >>
      qx_genl_tac [`m`, `dvs`, `g`] >>
      Cases_on `dvalues m0 d = SOME dvs` >> simp[] >> fs[] >>
      pop_assum kall_tac >>
      qabbrev_tac `vlist = REVERSE dvs` >>
      `∀x. MEM x dvs = MEM x vlist` by simp[Abbr`vlist`] >> fs[] >>
      ntac 2 (pop_assum kall_tac) >> pop_assum mp_tac >>
      map_every qid_spec_tac [`m`, `g`, `vlist`] >> Induct >>
      simp[EXISTS_PROD] >> dsimp[] >> rpt gen_tac >> strip_tac >> fs[PULL_FORALL] >>
      pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      rpt strip_tac >> res_tac >> simp[pcg_eval_merge_graph])
  >- ((* seq *)
      simp[graphOf_def, FOLDL_FOLDR_REVERSE] >> qx_gen_tac `cmds` >> strip_tac >>
      qx_genl_tac [`m`, `g`] >>
      qabbrev_tac `cs = REVERSE cmds` >>
      `∀x. MEM x cmds ⇔ MEM x cs` by simp[Abbr`cs`] >> fs[] >>
      ntac 2 (pop_assum kall_tac) >> pop_assum mp_tac >>
      map_every qid_spec_tac [`m`, `g`, `cs`] >> Induct >>
      simp[EXISTS_PROD] >> dsimp[] >> rpt strip_tac >>
      simp[pcg_eval_merge_graph] >> metis_tac[])
  >- ((* parloop *)
      map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      simp[graphOf_def, PULL_EXISTS, FORALL_PROD])
  >- ((* par *)
      qx_gen_tac `cs` >> simp[] >> strip_tac >>
      simp[Once graphOf_def, PULL_EXISTS])
  >- ((* assign *)
      simp[graphOf_def, FORALL_PROD, PULL_EXISTS] >>
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
  dsimp[INJ_IFF, EQ_IMP_THM] >> rw[]
  >- (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]));

val INJ_CONG = store_thm(
  "INJ_CONG",
  ``(∀x. x ∈ s ⇒ f x = g x) ⇒ (INJ f s t ⇔ INJ g s t)``,
  simp[INJ_IFF]);

val match_imp = let
  fun f th = SUBGOAL_THEN (lhand (concl th)) (mp_tac o MATCH_MP th)
in
  disch_then f
end

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

val _ = type_abbrev("pcnode", ``:(actionRW,α # (value list -> value))hinode``)
val _ = type_abbrev("pcg", ``:(actionRW,α # (value list -> value))hidag``)

val pcg_eval_NONE = store_thm(
  "pcg_eval_NONE[simp]",
  ``(∀n:α pcnode. pcn_eval n NONE = NONE) ∧
    ∀g:α pcg. pcg_eval g NONE = NONE``,
  ho_match_mp_tac hidag_ind >> simp[apply_action_def] >>
  rpt gen_tac >> Cases_on `a.writes` >> simp[]);

val addLabel_touches = store_thm(
  "addLabel_touches[simp]",
  ``(addLabel l a ∼ₜ b ⇔ a ∼ₜ b) ∧ (a ∼ₜ addLabel l b ⇔ a ∼ₜ b)``,
  simp[touches_def]);

val addLabel_gentouches = store_thm(
  "addLabel_gentouches[simp]",
  ``gentouches (set o action_reads) (set o action_writes) rf wf (addLabel l a) =
    gentouches (set o action_reads) (set o action_writes) rf wf a``,
  simp[FUN_EQ_THM, gentouches_def]);

val _ = overload_on("antouches",
  ``gentouches (set o action_reads) (set o action_writes) nreads nwrites``);

val ggentouches_add2 = store_thm(
  "ggentouches_add2[simp]",
  ``gentouches rf wf greads gwrites x (a <+ g) ⇔
      gentouches rf wf nreads nwrites x a ∨
      gentouches rf wf greads gwrites x g``,
  simp[gentouches_def] >> metis_tac[]);

val pcg_eval_expreval_preserves = store_thm(
  "pcg_eval_expreval_preserves",
  ``(∀n:α pcnode m0 m e.
        pcn_eval n (SOME m0) = SOME m ∧ ¬antouches (readAction () m0 e) n ⇒
        evalexpr m e = evalexpr m0 e ∧
        readAction () m e = readAction () m0 e) ∧
    ∀g:α pcg m0 m e.
       pcg_eval g (SOME m0) = SOME m ∧ ¬agtouches (readAction () m0 e) g ⇒
       evalexpr m e = evalexpr m0 e ∧
       readAction () m e = readAction () m0 e``,
  ho_match_mp_tac hidag_ind >> simp[pcg_eval_thm] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      match_mp_tac (apply_action_expr_eval_commutes
                      |> INST_TYPE [alpha |-> ``:one``, beta |-> ``:one``]) >>
      qexists_tac `polydata_upd SND a` >> simp[]) >>
  ntac 2 (rpt gen_tac >> strip_tac) >>
  `∃m'. pcn_eval n (SOME m0) = SOME m'`
    by (Cases_on `pcn_eval n (SOME m0)` >> fs[]) >>
  metis_tac[]);

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
  ``(∀n:'a pcnode m0 m1 m2.
      pcn_eval n (SOME m0) = SOME m1 ∧ apply_action a (SOME m0) = SOME m2 ∧
      ¬antouches a n ⇒
      ∃m. pcn_eval n (SOME m2) = SOME m ∧
          apply_action a (SOME m1) = SOME m) ∧
    ∀(g:'a pcg) m0 m1 m2.
      pcg_eval g (SOME m0) = SOME m1 ∧ apply_action a (SOME m0) = SOME m2 ∧
      ¬agtouches a g ⇒
      ∃m. pcg_eval g (SOME m2) = SOME m ∧
          apply_action a (SOME m1) = SOME m``,
  ho_match_mp_tac hidag_ind >>
  simp[pcg_eval_thm, DISJ_IMP_THM, FORALL_AND_THM] >> rpt conj_tac
  >- (rpt strip_tac >> match_mp_tac successful_action_diamond >>
      simp[] >> metis_tac[touches_SYM]) >>
  ntac 2 (rpt gen_tac >> strip_tac) >>
  `∃m'. pcn_eval n (SOME m0) = SOME m'`
    by (Cases_on `pcn_eval n (SOME m0)` >> fs[]) >> fs[] >> prove_tac[]);

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

val ggentouches_merge = store_thm(
  "ggentouches_merge[simp]",
  ``gentouches rf wf greads gwrites x (g1 ⊕ g2) ⇔
      gentouches rf wf greads gwrites x g1 ∨
      gentouches rf wf greads gwrites x g2``,
  simp[gentouches_def] >> metis_tac[]);

val ggentouches_empty = store_thm(
  "ggentouches_empty[simp]",
  ``(gentouches rf wf greads gwrites x ε ⇔ F) ∧
    (gentouches greads gwrites rf wf ε x ⇔ F)``,
  simp[gentouches_def]);

(*
val graphOf_apply_action_diamond = store_thm(
  "graphOf_apply_action_diamond",
  ``∀i0 m0 c m1 m2 a g.
      graphOf i0 m0 c = SOME(m1,g) ∧ apply_action a (SOME m0) = SOME m2 ∧
      ¬agtouches a g ⇒
      ∃m.
        graphOf i0 m2 c = SOME(m,g) ∧
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
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `evalexpr m2 gd = evalexpr m0 gd ∧
       readAction () m2 gd = readAction () m0 gd`
        by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
      simp[EXISTS_PROD])
  >- (map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      simp[graphOf_def, PULL_EXISTS, EXISTS_PROD, FOLDL_FOLDR_REVERSE] >>
      map_every qx_gen_tac [`m1`, `m2`, `a`, `dvs`, `g`] >> strip_tac >>
      `dvalues m2 d = dvalues m0 d ∧ domreadAction () m2 d = domreadAction () m0 d`
        by metis_tac[apply_action_dvalues_commutes] >> fs[] >>
      qpat_assum `domreadAction x y z = xx` kall_tac >>
      qpat_assum `dvalues x y = z` kall_tac >>
      Q.UNDISCH_THEN `a ≁ₜ domreadAction () m0 d` kall_tac >>
      Q.UNDISCH_THEN `dvalues m0 d = SOME dvs` kall_tac >>
      qabbrev_tac `vlist = REVERSE dvs` >>
      `∀x. MEM x dvs ⇔ MEM x vlist` by simp[Abbr`vlist`] >> fs[] >>
      ntac 2 (pop_assum kall_tac) >> rpt (pop_assum mp_tac) >>
      map_every qid_spec_tac [`g`, `m0`, `m1`, `m2`, `vlist`] >>
      Induct >> simp[EXISTS_PROD, PULL_EXISTS, DISJ_IMP_THM,
                     FORALL_AND_THM] >> rpt strip_tac >> rw[] >>
      fs[] >>
      qmatch_assum_rename_tac
        `FOLDR ff (SOME (m0,ε)) vlist = SOME (m',g1)` [] >>
      first_x_assum ((fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) o
                     assert (is_forall o concl)) >>
      prove_tac[])
  >- ((* seq *) qx_gen_tac `cmds` >>
      simp[graphOf_def, FOLDL_FOLDR_REVERSE] >> rpt strip_tac >>
      qabbrev_tac `clist = REVERSE cmds` >>
      `∀x. MEM x cmds ⇔ MEM x clist` by simp[Abbr`clist`] >> fs[] >>
      ntac 2 (pop_assum kall_tac) >> rpt (pop_assum mp_tac) >>
      map_every qid_spec_tac [`g`, `m0`, `m1`, `m2`, `clist`] >>
      Induct >> simp[EXISTS_PROD, PULL_EXISTS, DISJ_IMP_THM,
                     FORALL_AND_THM] >> rpt strip_tac >>
      qmatch_assum_rename_tac
        `FOLDR ff (SOME(m0,ε)) clist = SOME (m1',g')` [] >>
      rw[] >> fs[] >>
      first_x_assum ((fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) o
                     assert (is_forall o concl)) >>
      prove_tac[])
  >- ((* parloop *)
      map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      simp[PULL_EXISTS, EXISTS_PROD, graphOf_def] >>
      map_every qx_gen_tac [`m1`, `m2`, `a`, `dvs`, `gs`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `dvalues m2 d = dvalues m0 d ∧
       domreadAction () m2 d = domreadAction () m0 d`
        by metis_tac[apply_action_dvalues_commutes] >>
      simp[] >>
      qpat_assum `domreadAction x y z = u` kall_tac >>
      qpat_assum `dvalues m2 d = dvalues m0 d` kall_tac >>
      qpat_assum `a ≁ₜ domreadAction () m0 d` kall_tac >>
      qpat_assum `dvalues m0 d = SOME dvs` kall_tac >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `gs` >> simp[] >>
      `OPT_SEQUENCE
         (MAP (λv. OPTION_MAP SND (graphOf (v::i0) m2 (ssubst vnm v body)))
              dvs) =
       SOME gs`
        by (Induct_on `dvs` >> simp[]
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
  >- ((* malloc *) simp[graphOf_def]));

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
  >- ((* Malloc *) simp[graphOf_def]));

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



*)
val _ = export_theory();
