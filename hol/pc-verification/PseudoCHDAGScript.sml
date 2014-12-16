open HolKernel Parse boolLib bossLib;

open lcsymtacs
open actionTheory hidagTheory
open PseudoCTheory PseudoCPropsTheory
open bagTheory pairTheory pred_setTheory listTheory rich_listTheory
open indexedListsTheory
open finite_mapTheory
open intLib
open optionTheory
open relationTheory

open monadsyntax boolSimps

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

val _ = new_theory "PseudoCHDAG";

val _ = set_trace "Goalstack.print_goal_at_top" 0

val maRead_def = Define`
  (maRead m (VRead vnm) = SOME (vnm, [])) ∧
  (maRead m (ASub ae ie) =
     lift2 (λ(nm,is) n. (nm, is ++ [n]))
           (maRead m ae)
           (some n. evalexpr m ie = Int &n))
`;

val getReads_def = Define`
  (getReads m [] = SOME []) ∧
  (getReads m (DMA ma :: es) =
     lift2 CONS (maRead m ma) (getReads m es)) ∧
  (getReads m (DValue _ :: es) = getReads m es)
`;

val mergeReads0_def = Define`
  (mergeReads0 [] acc opn vs = opn (REVERSE acc)) ∧
  (mergeReads0 (DMA _ :: ds) acc opn vs =
     mergeReads0 ds (HD vs :: acc) opn (TL vs)) ∧
  (mergeReads0 (DValue v :: ds) acc opn vs =
     mergeReads0 ds (arrayError v :: acc) opn vs)
`;

val mergeReads_def = Define`
  mergeReads ds opn = mergeReads0 ds [] opn
`;

val evalDexpr_def = Define`
  (evalDexpr m (DValue v) = if isArrayError v then NONE else SOME v) ∧
  (evalDexpr m (DMA ma) = case evalmaccess m ma of
                              Error => NONE
                            | Array _ => NONE
                            | v => SOME v)
`;

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
  ``gentouches (set o action_reads) (set o action_write)
               (set o action_reads) (set o action_write) a1 a2 ⇔
      a1 ∼ₜ a2``,
  simp[touches_def, gentouches_def] >>
  map_every Cases_on [`a1.write`, `a2.write`] >>
  simp[] >> metis_tac[]);

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

val _ = type_abbrev("pcnode", ``:(actionRW,α # (value list -> value))hinode``)
val _ = type_abbrev("pcg", ``:(actionRW,α # (value list -> value))hidag``)

val pcg_eval_merge_graph = store_thm(
  "pcg_eval_merge_graph[simp]",
  ``pcg_eval (g1 ⊕ g2) m_opt = pcg_eval g2 (pcg_eval g1 m_opt)``,
  map_every qid_spec_tac [`m_opt`, `g2`, `g1`] >>
  Induct >> simp[]);

val pcg_eval_gflatten = store_thm(
  "pcg_eval_gflatten[simp]",
  ``(∀n:α pcnode. pcg_eval (nflatten n) = pcn_eval n) ∧
    (∀g:α pcg. pcg_eval (gflatten g) = pcg_eval g)``,
  ho_match_mp_tac hidag_ind >> simp[pcg_eval_merge_graph, FUN_EQ_THM]);

val _ = overload_on("strip_purereads", ``gafilter (IS_SOME o action_write)``)

val strip_purereads_OK = store_thm(
  "strip_purereads_OK",
  ``(∀n: α pcnode.
       pcn_eval n =
         case nafilter (IS_SOME o action_write) n of
             NONE => I
           | SOME n' => pcn_eval n') ∧
    (∀g: α pcg.    pcg_eval (strip_purereads g) = pcg_eval g)``,
  ho_match_mp_tac hidag_ind >> simp[FUN_EQ_THM] >> rpt strip_tac >|[
    COND_CASES_TAC >> simp[] >> fs[apply_action_def],
    COND_CASES_TAC >> fs[],
    Cases_on `nafilter (IS_SOME o action_write) n` >> fs[]
  ]);

val addLabel_def = Define`
  addLabel l a = polydata_upd (λv. (l,v)) a
`;

val dexpr_case_constant = store_thm(
  "dexpr_case_constant",
  ``dexpr_CASE d (λm. i) (λv. i) = i``,
  Cases_on `d` >> simp[]);

val stmt_weight_ssubst0 = store_thm(
  "stmt_weight_ssubst0[simp]",
  ``stmt_weight (K 0) (ssubst x y s) = stmt_weight (K 0) s``,
  qid_spec_tac `s` >> ho_match_mp_tac PseudoCTheory.stmt_induction >>
  simp[PseudoCTheory.ssubst_def, MAP_MAP_o, combinTheory.o_DEF,
       dexpr_case_constant,
       Cong (REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG)] >>
  reverse (rpt strip_tac) >- rw[] >>
  Cases_on `d` >> rw[PseudoCTheory.ssubst_def])

val mareadAction_def = Define`
  mareadAction l m ma =
    HD <| reads := SND (ma_reads m ma);
          write := NONE;
          data := (l,ARB:value list -> value);
          ident := () |>
`;


val mlt_BAG_IMAGE_SUC = store_thm(
  "mlt_BAG_IMAGE_SUC[simp]",
  ``FINITE_BAG b ∧ b ≠ {||} ⇒ mlt $< b (BAG_IMAGE SUC b)``,
  simp[mlt_dominates_thm1] >> strip_tac >>
  map_every qexists_tac [`BAG_IMAGE SUC b`, `b`] >>
  simp[dominates_def, PULL_EXISTS] >> metis_tac[DECIDE ``x < SUC x``])

val SUM_MAP_lemma = store_thm(
  "SUM_MAP_lemma",
  ``∀l. MEM e l ⇒ f e < LENGTH l + SUM (MAP f l)``,
  Induct >> dsimp[] >> rpt strip_tac >> res_tac >> simp[]);

(* ----------------------------------------------------------------------
    Create an action graph from a PseudoC program.

    Function is partial to allow for possibility that actions
    parallelised underneath a Par may be touching/conflicting. If this
    happens, the result has to be NONE.

    The function will also return NONE if there are constructs within the
    program that are not allowed to appear in "original code" programs.
   ---------------------------------------------------------------------- *)

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

  (graphOf lab m0 (ForLoop vnm d body) =
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
       SOME(m, HD (addLabel lab (domreadAction () m0 d)) <+ g)
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

  (graphOf i0 m0 (Assign ma ds opn) =
     do
        lv <- eval_lvalue m0 ma;
        rds <- getReads m0 ds;
        a0 <- SOME (mareadAction i0 m0 ma);
        a1 <- SOME (HD (addLabel i0 (dvreadAction () m0 ds)));
        a <- SOME (HD <| write := SOME lv;
                         reads := rds;
                         data := (i0, mergeReads ds opn);
                         ident := () |>) ;
        rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
        m' <- upd_write m0 ma opn rvs;
        SOME(m', a0 <+ a1 <+ a <+ ε)
     od) ∧

  (graphOf i0 m0 Abort = NONE) ∧

  (graphOf i0 m0 Done = SOME(m0,ε)) ∧

  (graphOf i0 m0 (Malloc vnm sz value) = NONE) ∧

  (graphOf i0 m0 (Label v s) = graphOf (v::i0) m0 s) ∧

  (graphOf lab m0 (Local v e s) =
     do
       value <- SOME(evalexpr m0 e);
       assert(¬isArrayError value);
       (m,g) <- graphOf lab m0 (ssubst v value s);
       SOME(m,HD (addLabel lab (readAction () m0 e)) <+ g)
     od) ∧

  (graphOf lab m (Atomic s) = NONE) ∧

  (graphOf lab m (While g b) = NONE) ∧

  (graphOf lab m (WaitUntil g) = NONE)
` (WF_REL_TAC
     `inv_image (mlt (<) LEX (<)) (λ(i,m,s). (loopbag s, stmt_weight (K 0) s))` >>
   simp[WF_mlt1, FOLDR_MAP, mlt_loopbag_lemma] >>
   rpt strip_tac >> TRY (rw[mlt_loopbag_lemma, MAX_PLUS] >> NO_TAC) >>
   imp_res_tac MEM_FOLDR_mlt >> pop_assum (qspec_then `I` mp_tac) >>
   rw[SUM_MAP_lemma])

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

val OPT_SEQUENCE_EQ_SOME = store_thm(
   "OPT_SEQUENCE_EQ_SOME",
   ``∀l. OPT_SEQUENCE optlist = SOME l ⇔
         (∀e. MEM e optlist ⇒ ∃v. e = SOME v) ∧
         (l = MAP THE optlist)``,
   Induct_on `optlist` >> dsimp[OPT_SEQUENCE_def] >>
   csimp[] >> metis_tac []);

val some_EQ_SOME_E = save_thm(
  "some_EQ_SOME_E",
  some_elim
    |> Q.INST [`Q` |-> `\y. y = SOME x`]
    |> SIMP_RULE bool_ss [NOT_SOME_NONE,
                          SOME_11]);

val some_EQ_NONE = store_thm(
  "some_EQ_NONE[simp]",
  ``(some) P = NONE ⇔ ∀x. ¬P x``,
  DEEP_INTRO_TAC some_intro THEN
  SIMP_TAC bool_ss [NOT_SOME_NONE] THEN
  METIS_TAC[]);

val OPTION_MAP2_STRICT = store_thm(
  "OPTION_MAP2_STRICT[simp]",
  ``OPTION_MAP2 f NONE y = NONE ∧
    OPTION_MAP2 f x NONE = NONE``,
  Cases_on `x` >> Cases_on `y` >> simp[]);

val value_case_K = store_thm(
  "value_case_K[simp]",
  ``value_CASE value (λv. x) (λv. x) (λv. x) (λv. x) x = x``,
  Cases_on `value` >> simp[]);

val evalmaccess_maRead = save_thm(
  "evalmaccess_maRead",
  prove(``(∀e:expr. T) ∧
    ∀ma m nm is.
      evalmaccess m ma =
        case maRead m ma of
            SOME (nm,is) => lookup_indices (lookup_v m nm) is
          | NONE => Error``,
  ho_match_mp_tac expr_ind' >>
  simp[maRead_def, evalexpr_def, EXISTS_PROD, PULL_EXISTS,
       lookup_indices_APPEND] >>
  rpt strip_tac >>
  `maRead m ma = NONE ∨ ∃nm0 is. maRead m ma = SOME(nm0,is)`
    by metis_tac[pair_CASES, option_CASES] >>
  simp[] >>
  Cases_on `evalexpr m e` >> simp[] >>
  `(∃n. i = -&n ∧ n ≠ 0) ∨ ∃n. i = &n`
    by metis_tac[integerTheory.INT_NUM_CASES] >> simp[] >>
  simp[lookup_indices_APPEND] >>
  Cases_on `lookup_indices (lookup_v m nm0) is` >> simp[] >>
  rw[] >> lfs[]) |> CONJUNCT2);

val isArrayError_ID = store_thm(
  "isArrayError_ID",
  ``(¬isArrayError v ⇒ arrayError v = v) ∧
    (¬isArray v ⇒ arrayError v = v)``,
  Cases_on `v` >> simp[]);

val assign_lemma = store_thm(
  "assign_lemma",
  ``OPT_SEQUENCE (MAP (evalDexpr m) ds) = SOME rvs ∧
    getReads m ds = SOME rds ⇒
    mergeReads0 ds acc opn (MAP (lookupRW m) rds) =
    (opn:value list -> value) (REVERSE acc ++ rvs)``,
  csimp[OPT_SEQUENCE_EQ_SOME, MEM_MAP, MAP_MAP_o, PULL_EXISTS,
        EVERY_MEM] >>
  map_every qid_spec_tac [`acc`, `rvs`, `rds`, `ds`] >> simp[] >>
  Induct >> simp[getReads_def, mergeReads0_def] >>
  Cases >> dsimp[getReads_def, mergeReads0_def, evalDexpr_def,
                 lookupRW_def, isArrayError_ID, value_case_eq] >>
  simp_tac bool_ss [APPEND, GSYM APPEND_ASSOC] >>
  csimp[lookupRW_lookup_indices, evalmaccess_maRead, FORALL_PROD,
        maRead_def, isArrayError_ID]);

val addLabel_readswrites = store_thm(
  "addLabel_readswrites[simp]",
  ``(addLabel l a).reads = a.reads ∧ (addLabel l a).write = a.write``,
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
  TRY (simp[graphOf_def] >> NO_TAC) >>
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
      csimp[graphOf_def, FORALL_PROD, PULL_EXISTS, apply_action_def,
            upd_memory_def, mareadAction_def, upd_write_def] >>
      map_every qx_gen_tac [`w`, `ds`, `opn`, `m`, `wnm`, `wis`, `rds`, `rvs`] >>
      strip_tac >>
      `mergeReads ds opn (MAP (lookupRW m0) rds) = opn rvs` suffices_by simp[] >>
      imp_res_tac (GEN_ALL assign_lemma) >> simp[mergeReads_def])
  >- ((* Local *) simp[graphOf_def, EXISTS_PROD, PULL_EXISTS])
);

val assert_EQ_SOME = store_thm(
  "assert_EQ_SOME[simp]",
  ``(assert b = SOME x) <=> b``,
  Cases_on `b` THEN SIMP_TAC (srw_ss()) [oneTheory.one]);

val graphOf_simps = save_thm(
  "graphOf_simps[simp]",
  LIST_CONJ
    [ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 Done``,
     ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 Abort``,
     ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 (Malloc vn n v)``,
     ONCE_REWRITE_CONV [graphOf_def] ``graphOf i0 m0 (Label v s)``
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
  simp[evalDexpr_def] >> Cases_on `v` >> simp[]);

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
  Cases_on `h` >> simp[getReads_def, lift2_lift2_1, lift2_lift2_2]);

val pcg_eval_NONE = store_thm(
  "pcg_eval_NONE[simp]",
  ``(∀n:α pcnode. pcn_eval n NONE = NONE) ∧
    ∀g:α pcg. pcg_eval g NONE = NONE``,
  ho_match_mp_tac hidag_ind >> simp[apply_action_def] >>
  rpt gen_tac >> Cases_on `a.write` >> simp[]);

val addLabel_touches = store_thm(
  "addLabel_touches[simp]",
  ``(addLabel l a ∼ₜ b ⇔ a ∼ₜ b) ∧ (a ∼ₜ addLabel l b ⇔ a ∼ₜ b)``,
  simp[touches_def]);

val addLabel_gentouches = store_thm(
  "addLabel_gentouches[simp]",
  ``gentouches (set o action_reads) (set o action_write) rf wf (addLabel l a) =
    gentouches (set o action_reads) (set o action_write) rf wf a``,
  simp[FUN_EQ_THM, gentouches_def]);

val _ = overload_on("antouches",
  ``gentouches (set o action_reads) (set o action_write) nreads nwrites``);

val pcg_eval_expreval_preserves = store_thm(
  "pcg_eval_expreval_preserves",
  ``(∀n:α pcnode m0 m e.
        ¬isArrayError (evalexpr m0 e) ∧
        pcn_eval n (SOME m0) = SOME m ∧ ¬antouches (readAction () m0 e) n ⇒
        evalexpr m e = evalexpr m0 e ∧
        readAction () m e = readAction () m0 e) ∧
    ∀g:α pcg m0 m e.
        ¬isArrayError (evalexpr m0 e) ∧
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
  ``devals_scalar m0 d ∧ apply_action a (SOME m0) = SOME m ∧
    a ≁ₜ domreadAction i m0 d ⇒
    dvalues m d = dvalues m0 d ∧ domreadAction i m d = domreadAction i m0 d``,
  `∃e1 e2. d = D e1 e2` by (Cases_on `d` >> simp[]) >>
  simp[domreadAction_def, touches_def, devals_scalar_def] >> strip_tac >>
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
    by metis_tac[nontouching_updm_expreval, touches_SYM] >>
  simp[] >>
  rfs[touches_def] >> metis_tac[successful_upd_memory_diamond]);

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

val dexprOK_def = Define`
  (dexprOK m (DMA e) = ¬isArrayError (evalmaccess m e)) ∧
  (dexprOK m (DValue v) = ¬isArrayError v)
`;
val _ = export_rewrites ["dexprOK_def"]

val maRead_ma_reads = save_thm(
  "maRead_ma_reads",
  prove(
    ``(∀e:expr. T) ∧ (∀ma. maRead m ma = FST (ma_reads m ma))``,
  ho_match_mp_tac expr_ind' >> simp[expr_reads_def, maRead_def] >>
  rpt strip_tac >>
  Cases_on `ma_reads m ma` >> simp[] >>
  Cases_on `evalexpr m e` >> simp[] >>
  qmatch_assum_rename_tac `ma_reads m ma = (lvopt, rds)` [] >> fs[] >>
  Cases_on `lvopt` >> simp[] >>
  qmatch_assum_rename_tac `maRead m ma = SOME lv` [] >>
  Cases_on `lv` >> simp[] >>
  qmatch_assum_rename_tac `evalexpr m e = Int i` [] >>
  `(∃n. i = &n) ∨ (∃n. i = -&n ∧ n ≠ 0)`
    by metis_tac[integerTheory.INT_NUM_CASES] >> simp[])
  |> CONJUNCT2);

val ma_reads_NONE_Error = save_thm(
  "ma_reads_NONE_Error",
  prove(``(∀e:expr. T) ∧
    ∀ma m rds. ma_reads m ma = (NONE, rds) ⇒
               evalmaccess m ma = Error``,
  ho_match_mp_tac expr_ind' >>
  simp[expr_reads_def, evalexpr_def, pair_case_eq, value_case_eq,
       option_case_eq, bool_case_eq, PULL_EXISTS] >>
  rpt strip_tac >> veq >> res_tac >> simp[] >>
  Cases_on `evalmaccess m ma` >> simp[] >>
  asm_simp_tac (srw_ss() ++ intSimps.OMEGA_ss) []) |> CONJUNCT2);

val apply_action_dvreadAction_commutes = store_thm(
  "apply_action_dvreadAction_commutes",
  ``a ≁ₜ dvreadAction i m0 ds ∧ apply_action a (SOME m0) = SOME m ∧
    getReads m0 ds = SOME rds ∧ (∀d. MEM d ds ⇒ dexprOK m0 d) ∧
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
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `apply_action a (SOME m0) = SOME m` >> simp[] >>
  ntac 2 (pop_assum mp_tac) >>
  ntac 2 strip_tac >> strip_tac >>
  ntac 4 (pop_assum mp_tac) >>
  qid_spec_tac `rds` >> Induct_on `ds` >>
  simp[getReads_def] >> Cases >> simp[getReads_def, dvread_def, evalDexpr_def] >>
  simp[dvread_def, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
  simp[PULL_FORALL] >> qx_genl_tac [`lv`, `rds`] >> ntac 4 strip_tac >>
  qmatch_assum_rename_tac `maRead m0 mref = SOME lv` [] >>
  `readAction () m0 (MAccess mref) ≁ₜ a`
    by simp[touches_def, readAction_def, expr_reads_def] >>
  `¬isArrayError (evalexpr m0 (MAccess mref))` by simp[evalexpr_def] >>
  `evalexpr m (MAccess mref) = evalexpr m0 (MAccess mref) ∧
   readAction () m (MAccess mref) = readAction () m0 (MAccess mref)`
    by metis_tac[apply_action_expr_eval_commutes] >>
  fs[evalexpr_def, readAction_def, expr_reads_def] >>
  fs[maRead_ma_reads] >> Cases_on `ma_reads m0 mref` >> fs[] >> veq >>
  fs[pair_case_eq, option_case_eq] >> veq >>
  `evalmaccess m mref = Error` by imp_res_tac ma_reads_NONE_Error >> fs[] >>
  metis_tac[isArrayError_DISJ_EQ])

val agentouches_polydata_upd = store_thm(
  "agentouches_polydata_upd[simp]",
  ``(gentouches (set o action_reads) (set o action_write) rf wf
       (polydata_upd f a) x ⇔
     gentouches (set o action_reads) (set o action_write) rf wf a x) ∧
    (gentouches rf wf (set o action_reads) (set o action_write)
       x (polydata_upd f a) ⇔
     gentouches rf wf (set o action_reads) (set o action_write) x a)``,
  simp[gentouches_def]);

val maccess_ind = save_thm(
  "maccess_ind",
  expr_ind' |> SPEC ``λe:expr. T`` |> SIMP_RULE bool_ss [])

val eval_lvalue_SOME = store_thm(
  "eval_lvalue_SOME",
  ``∀ma lv m.
      eval_lvalue m ma = SOME lv ⇒
      ∃rds. ma_reads m ma = (SOME lv, rds)``,
  ho_match_mp_tac maccess_ind >>
  simp[eval_lvalue_def, EXISTS_PROD, expr_reads_def, PULL_EXISTS] >>
  qx_genl_tac [`ma`, `ie`] >> strip_tac >>
  qx_genl_tac [`m`, `vnm`, `is`, `i`]>> strip_tac >> res_tac >>
  simp[] >> Cases_on `evalexpr m ie` >> fs[])

val apply_action_eval_lvalue_commutes = store_thm(
  "apply_action_eval_lvalue_commutes",
  ``∀lv a l m0 m anm is.
       ¬antouches a (mareadAction l m0 lv) ∧ apply_action a (SOME m0) = SOME m ∧
       eval_lvalue m0 lv = SOME (anm, is) ⇒
       eval_lvalue m lv = SOME (anm, is) ∧
       mareadAction l m lv = mareadAction l m0 lv``,
  ho_match_mp_tac maccess_ind >>
  simp[mareadAction_def, touches_def, eval_lvalue_def, EXISTS_PROD,
       PULL_EXISTS, expr_reads_def] >>
  qx_genl_tac [`lv`, `ie`] >> strip_tac >>
  qx_genl_tac [`a`, `m0`, `m`, `vnm`, `is`, `i`] >> strip_tac >>
  Cases_on `evalexpr m0 ie` >> fs[] >> veq >>
  imp_res_tac eval_lvalue_SOME >> fs[] >>
  `eval_lvalue m lv = SOME(vnm,is)` by metis_tac[SND] >>
  `∃mrds. ma_reads m lv = (SOME(vnm,is), mrds)` by metis_tac[eval_lvalue_SOME]>>
  simp[] >>
  `readAction () m0 ie ≁ₜ a`
    by (simp[readAction_def, touches_def, FORALL_PROD] >> metis_tac[]) >>
  `¬isArrayError (evalexpr m0 ie)` by simp[] >>
  `readAction () m ie = readAction () m0 ie ∧ evalexpr m ie = evalexpr m0 ie`
    by metis_tac[apply_action_expr_eval_commutes] >> simp[] >>
  fs[readAction_def] >> metis_tac[SND])

val evalDexpr_dexprOK = store_thm(
  "evalDexpr_dexprOK",
  ``∀ds m rvs. OPT_SEQUENCE (MAP (evalDexpr m) ds) = SOME rvs ⇒
               ∀d. MEM d ds ⇒ dexprOK m d``,
  dsimp[OPT_SEQUENCE_EQ_SOME, MEM_MAP] >> Induct >> dsimp[] >>
  Cases >> simp[evalDexpr_def, value_case_eq] >> dsimp[]);

val evalDexpr_notArrayError = store_thm(
  "evalDexpr_notArrayError",
  ``∀ds m rvs. OPT_SEQUENCE (MAP (evalDexpr m) ds) = SOME rvs ⇒
               ∀v. MEM v rvs ⇒ ¬isArrayError v``,
  dsimp[OPT_SEQUENCE_EQ_SOME, MEM_MAP] >> rpt strip_tac >> res_tac >>
  qmatch_assum_rename_tac `MEM y ds` [] >> Cases_on `y` >>
  fs[evalDexpr_def, value_case_eq] >> veq >> fs[]);

val graphOf_apply_action_diamond = store_thm(
  "graphOf_apply_action_diamond",
  ``∀i0 m0 c m1 m2 a g.
      graphOf i0 m0 c = SOME(m1,g) ∧ apply_action a (SOME m0) = SOME m2 ∧
      ¬agtouches a g ⇒
      ∃m.
        graphOf i0 m2 c = SOME(m,g) ∧
        apply_action a (SOME m1) = SOME m``,
  ho_match_mp_tac (theorem "graphOf_ind") >> rpt conj_tac >>
  TRY (simp[graphOf_def] >> NO_TAC) >>
  map_every qx_gen_tac [`i0`, `m0`]
  >- ((* if *)
      qx_gen_tac `gd` >> rpt gen_tac >> strip_tac >> simp[graphOf_def] >>
      rpt gen_tac >>
      Cases_on `evalexpr m0 gd` >> simp[] >>
      qmatch_assum_rename_tac `evalexpr m0 gd = Bool b` [] >>
      Cases_on `b` >> fs[] >> simp[PULL_EXISTS, EXISTS_PROD] >>
      qx_gen_tac `g'` >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `¬isArrayError (evalexpr m0 gd)` by simp[] >>
      `evalexpr m2 gd = evalexpr m0 gd ∧
       readAction () m2 gd = readAction () m0 gd`
        by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
      simp[EXISTS_PROD])
  >- (map_every qx_gen_tac [`vnm`, `d`, `body`] >> strip_tac >>
      simp[graphOf_def, PULL_EXISTS, EXISTS_PROD, FOLDL_FOLDR_REVERSE] >>
      map_every qx_gen_tac [`m1`, `m2`, `a`, `dvs`, `g`] >> strip_tac >>
      `devals_scalar m0 d` by imp_res_tac dvalues_SOME_devals_scalar >>
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
      simp[PULL_EXISTS, EXISTS_PROD, graphOf_def, OPT_SEQUENCE_EQ_SOME,
           EL_MAP, MEM_MAP, PULL_EXISTS,
           MAP_EQ_f, MAP_MAP_o, combinTheory.o_ABS_R] >>
      qabbrev_tac
        `TOS =
           λv m. THE (OPTION_MAP SND (graphOf (v::i0) m (ssubst vnm v body)))` >>
      simp[] >>
      qx_genl_tac [`m1`, `m2`, `a`, `dvs`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      `devals_scalar m0 d` by imp_res_tac dvalues_SOME_devals_scalar >>
      `dvalues m2 d = dvalues m0 d ∧
       domreadAction () m2 d = domreadAction () m0 d`
        by metis_tac[apply_action_dvalues_commutes] >>
      simp[] >>
      qpat_assum `domreadAction x y z = u` kall_tac >>
      qpat_assum `dvalues m2 d = dvalues m0 d` kall_tac >>
      qpat_assum `a ≁ₜ domreadAction () m0 d` kall_tac >>
      qpat_assum `dvalues m0 d = SOME dvs` kall_tac >>
      `∀l. FOLDR (λg:value list pcg acc. HG g <+ acc) ε l = hdbuild (MAP HG l)`
        by simp[FOLDR_MAP] >> fs[MAP_MAP_o, combinTheory.o_ABS_R, MEM_MAP] >>
      `∀dv. MEM dv dvs ⇒
            (∃m'. graphOf (dv::i0) m2 (ssubst vnm dv body) =
                  SOME (m',TOS dv m0)) ∧
            TOS dv m2 = TOS dv m0`
        by (gen_tac >> strip_tac >>
            `∃m' g'. graphOf (dv::i0) m0 (ssubst vnm dv body) = SOME (m',g')`
              by metis_tac[] >>
            first_x_assum (qspec_then `HG (TOS dv m0)` strip_assume_tac)
            >- metis_tac[] >> fs[] >>
            `TOS dv m0 = g'` by simp[Abbr`TOS`] >> fs[] >>
            `∃m. graphOf (dv::i0) m2 (ssubst vnm dv body) = SOME (m, g')`
              by metis_tac[] >>
            simp[Abbr`TOS`]) >>
      simp[GSYM PULL_EXISTS] >> rpt conj_tac
      >- metis_tac[]
      >- (simp[OPTION_GUARD_EQ_THM, oneTheory.one] >>
          metis_tac[MEM_EL, DECIDE ``i < j ∧ j < n ⇒ i < n:num``]) >>
      `MAP (λv. HG (TOS v m2)) dvs = MAP (λv. HG (TOS v m0)) dvs`
        by simp[MAP_EQ_f] >> simp[] >>
      `¬agtouches a (hdbuild (MAP (λv. HG (TOS v m0)) dvs))`
        by simp[MEM_MAP] >>
      metis_tac[pcg_eval_apply_action_diamond])
  >- ((* par *)
      qx_gen_tac `cmds` >> strip_tac >> qx_genl_tac [`m1`, `m2`, `a`, `g`] >>
      simp[graphOf_def, OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R, PULL_EXISTS,
           MEM_MAP, EL_MAP, MAP_MAP_o, EXISTS_PROD] >>
      qabbrev_tac `TOS = λc m. THE (OPTION_MAP SND (graphOf i0 m c))` >>
      simp[] >>
      `∀l. FOLDR (λg:value list pcg acc. HG g <+ acc) ε l = hdbuild (MAP HG l)`
        by simp[FOLDR_MAP] >> fs[MAP_MAP_o, combinTheory.o_ABS_R, MEM_MAP] >>
      strip_tac >> rw[] >> fs[MEM_MAP] >>
      `∀c. MEM c cmds ⇒
            (∃m'. graphOf i0 m2 c = SOME (m',TOS c m0)) ∧
            TOS c m2 = TOS c m0`
        by (gen_tac >> strip_tac >>
            `∃m' g'. graphOf i0 m0 c = SOME (m',g')` by metis_tac[] >>
            first_x_assum (qspec_then `HG (TOS c m0)` strip_assume_tac)
            >- metis_tac[] >> fs[] >>
            `TOS c m0 = g'` by simp[Abbr`TOS`] >> fs[] >>
            `∃m. graphOf i0 m2 c = SOME (m, g')` by metis_tac[] >>
            simp[Abbr`TOS`]) >>
      simp[GSYM PULL_EXISTS, GSYM CONJ_ASSOC] >> rpt conj_tac
      >- metis_tac[]
      >- (simp[oneTheory.one] >>
          metis_tac[MEM_EL, DECIDE ``i < j ∧ j < n ⇒ i < n:num``]) >>
      `MAP (λc. HG (TOS c m2)) cmds = MAP (λc. HG (TOS c m0)) cmds`
        by simp[MAP_EQ_f] >> simp[] >>
      `¬agtouches a (hdbuild (MAP (λc. HG (TOS c m0)) cmds))`
        by simp[MEM_MAP] >>
      metis_tac[pcg_eval_apply_action_diamond])
  >- ((* assign *)
      simp[graphOf_def, FORALL_PROD, PULL_EXISTS] >>
      qx_genl_tac [`lv`, `ds`, `opn`, `m1`, `m2`, `a`, `anm`, `is`,
                   `rds`, `rvs`] >> strip_tac >>
      `eval_lvalue m2 lv = SOME (anm, is) ∧
       mareadAction i0 m2 lv = mareadAction i0 m0 lv`
        by metis_tac[apply_action_eval_lvalue_commutes] >> simp[] >>
      `IS_SOME a.write ⇒ ¬MEM (THE a.write) rds`
        by (Cases_on `a.write` >> fs[touches_def] >> metis_tac[]) >>
      `∀d. MEM d ds ⇒ dexprOK m0 d` by metis_tac[evalDexpr_dexprOK] >>
      `getReads m2 ds = getReads m0 ds ∧
       dvreadAction () m2 ds = dvreadAction () m0 ds ∧
       MAP (evalDexpr m2) ds = MAP (evalDexpr m0) ds`
        by metis_tac[apply_action_dvreadAction_commutes] >> simp[] >>
      qabbrev_tac `b = <|
        reads := []; write := SOME (anm,is); ident := ();
        data := K (opn rvs) : value list -> value |>` >>
      `EVERY ($~ o isArrayError) rvs`
        by (simp[EVERY_MEM] >> metis_tac[evalDexpr_notArrayError]) >>
      `upd_write m2 lv opn rvs = apply_action b (SOME m2)`
        by simp[apply_action_def, Abbr`b`, upd_write_def] >> fs[] >>
      `a ≁ₜ b` by (simp[touches_def, Abbr`b`] >> fs[touches_def] >>
                   Cases_on `a.write` >> fs[]) >>
      `apply_action b (SOME m0) = SOME m1`
        by (fs[apply_action_def, Abbr`b`, upd_write_def] >> rfs[]) >>
      metis_tac[successful_action_diamond])
  >- ((* Local *) simp[graphOf_def, EXISTS_PROD, PULL_EXISTS] >>
      rpt strip_tac >> fs[] >>
      `evalexpr m2 e = evalexpr m0 e ∧ readAction () m2 e = readAction () m0 e`
        by metis_tac[apply_action_expr_eval_commutes, touches_SYM] >>
      simp[])
)

val graphOf_pcg_eval_diamond = store_thm(
  "graphOf_pcg_eval_diamond",
  ``(∀n:value list pcnode m0 m1 i c m2 g.
      pcn_eval n (SOME m0) = SOME m1 ∧
      graphOf i m0 c = SOME(m2,g) ∧
      ¬gentouches nreads nwrites greads gwrites n g ⇒
      ∃m2'. graphOf i m1 c = SOME(m2',g) ∧
            pcn_eval n (SOME m2) = SOME m2') ∧
    ∀g1 m0 m1 i c m2 g2.
      pcg_eval g1 (SOME m0) = SOME m1 ∧
      graphOf i m0 c = SOME(m2,g2) ∧
      ¬gtouches g1 g2 ⇒
      ∃m2'. graphOf i m1 c = SOME(m2',g2) ∧
            pcg_eval g1 (SOME m2) = SOME m2'``,
  ho_match_mp_tac hidag_ind >> simp[pcg_eval_thm] >> rpt strip_tac
  >- (match_mp_tac graphOf_apply_action_diamond >>
      simp[] >> metis_tac[]) >>
  `∃m'. pcn_eval n (SOME m0) = SOME m'` suffices_by metis_tac[] >>
  Cases_on `pcn_eval n (SOME m0)` >> fs[]);

val graphOfL_def = Define`
  graphOfL lf cf i0 mg0 x = do
    (m0,g0) <- mg0;
    (m,g) <- graphOf (lf x i0) m0 (cf x);
    SOME(m,g0 ⊕ HG g <+ ε)
  od
`

val forcase =
    graphOfL_def |> INST_TYPE [alpha |-> ``:value``,
                               beta |-> ``:value list``]
                 |> Q.SPECL [`CONS`, `λv. ssubst vnm v body`, `i0`]
                 |> BETA_RULE

val seqcase =
    graphOfL_def |> INST_TYPE [alpha |-> ``:stmt``,
                               beta |-> ``:value list``]
                 |> Q.SPECL [`K I`, `I`]
                 |> SIMP_RULE (srw_ss()) []

val graphOf_def' =
    SIMP_RULE (bool_ss ++ boolSimps.ETA_ss) [GSYM forcase, GSYM seqcase] graphOf_def

val _ = overload_on("MergeL", ``FOLDR hdmerge ε``)

val MergeL_empties = store_thm(
  "MergeL_empties",
  ``(∀g. MEM g glist ⇒ g = ε) ⇒ MergeL glist = ε``,
  Induct_on `glist` >> simp[]);

val FOLDL_graphOfL_Dones = store_thm(
  "FOLDL_graphOfL_Dones[simp]",
  ``∀l m g.
      EVERY ($= Done) l ⇒
      FOLDL (graphOfL lf I lab) (SOME(m,g)) l =
      SOME (m, g ⊕ MergeL (GENLIST (K (HG ε <+ ε)) (LENGTH l)))``,
  Induct >> simp[graphOfL_def, GENLIST_CONS] >> simp[GSYM hdmerge_ASSOC])

val FOLDL_graphOfL_EQ_NONE = store_thm(
  "FOLDL_graphOfL_EQ_NONE[simp]",
  ``∀l. FOLDL (graphOfL lf cf lab) NONE l = NONE``,
  Induct >> simp[graphOfL_def]);

val FOLDL_graphOfL_EQ_SOME_E = store_thm(
  "FOLDL_graphOfL_EQ_SOME_E",
  ``FOLDL (graphOfL lf cf lab) a l = SOME(m,g) ⇒
    ∃m0 g0. a = SOME(m0,g0)``,
  `a = NONE ∨ ∃m g. a = SOME(m,g)`
    by metis_tac[option_CASES, pair_CASES] >>
  simp[]);

val FOLDL_graphOfL_allnodes = store_thm(
  "FOLDL_graphOfL_allnodes",
  ``∀l m0 g0 m g.
      FOLDL (graphOfL lf cf lab) (SOME(m0,g0)) l = SOME(m,g) ⇒
      ∀a. BAG_IN a (allnodes g0) ⇒ BAG_IN a (allnodes g)``,
  Induct >> simp[graphOfL_def] >> rpt gen_tac >>
  strip_tac >>
  imp_res_tac FOLDL_graphOfL_EQ_SOME_E >>
  pop_assum (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                      mp_tac th) >> simp[EXISTS_PROD] >> res_tac >>
  rw[] >> fs[]);

val IN_allnodes_FOLDR_HGadd = store_thm(
  "IN_allnodes_FOLDR_HGadd[simp]",
  ``a <: allnodes (FOLDR (λg acc. HG g <+ acc) g0 l) ⇔
    a <: allnodes g0 ∨ ∃e. MEM e l ∧ a <: allnodes e``,
  Induct_on `l` >> simp[] >> metis_tac[]);

val eval_graphOf_action = store_thm(
  "eval_graphOf_action",
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      m0 ≠ m ⇒
      ∀i0 m0' g0.
        graphOf i0 m0 c0 = SOME(m0', g0) ⇒
        ∃a. BAG_IN a (allnodes g0) ∧
            apply_action (polydata_upd SND a) (SOME m0) = SOME m``,
  ho_match_mp_tac eval_ind' >> rpt conj_tac >> REWRITE_TAC [] >>
  TRY (simp[graphOf_def] >> NO_TAC)
  >- ((* member of Seq steps *)
      map_every qx_gen_tac [`c`, `c0`, `pfx`, `sfx`, `m0`, `m`] >>
      ntac 2 strip_tac >> fs[] >> simp[graphOf_def'] >>
      simp[FOLDL_APPEND, graphOfL_def] >>
      qx_genl_tac [`i0`, `m'`, `g'`] >>
      disch_then (fn th =>
                     (th |> MATCH_MP FOLDL_graphOfL_EQ_SOME_E
                         |> qx_choosel_then [`mm`, `gg`] mp_tac) >>
                     assume_tac th) >>
      disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                           mp_tac th) >>
      simp[EXISTS_PROD] >>
      disch_then (qx_choosel_then [`gg0`] strip_assume_tac) >>
      `∃a. BAG_IN a (allnodes gg0) ∧
           apply_action (polydata_upd SND a) (SOME m0) = SOME m`
        by metis_tac[] >>
      qexists_tac `a` >> simp[] >> imp_res_tac FOLDL_graphOfL_allnodes >>
      rw[] >> fs[allnodes_def])
  >- ((* assign *)
      simp[graphOf_def, PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      rpt strip_tac >> dsimp[] >>
      simp[apply_action_def, mergeReads_def, readAction_def,
           dvreadAction_def] >>
      imp_res_tac assign_lemma >> simp[] >> fs[upd_write_def] >> fs[] >>
      veq >> fs[mareadAction_def] >>
      `MAP destDValue rdes = rvs` suffices_by (strip_tac >> fs[]) >>
      full_simp_tac (srw_ss() ++ DNF_ss)
        [OPT_SEQUENCE_EQ_SOME, MEM_MAP, EVERY_MEM] >>
      simp[MAP_EQ_f, MAP_MAP_o] >> Cases >>
      simp[evalDexpr_def] >> strip_tac >> res_tac >> fs[] >>
      Cases_on `v` >> fs[])
  >- ((* par *)
      map_every qx_gen_tac [`m0`, `m`, `pfx`, `c0`, `c`, `sfx`] >> strip_tac >>
      strip_tac >> fs[] >>
      simp[graphOf_def, oneTheory.one, MAP_MAP_o,
           PULL_EXISTS, OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R] >>
      qabbrev_tac `
        TOS = λi m c. THE (OPTION_MAP SND (graphOf i m c))` >> simp[] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, EXISTS_PROD] >>
      qx_genl_tac [`i0`, `m'`] >> strip_tac >>
      qmatch_assum_rename_tac `graphOf i0 m0 c0 = SOME(mm,gg)` [] >>
      `TOS i0 m0 c0 = gg` by simp[Abbr`TOS`] >> metis_tac[])
  >- ((* Label *) simp[graphOf_def] >> metis_tac[])
);

val hdbuild_append = store_thm(
  "hdbuild_append[simp]",
  ``hdbuild (l1 ++ l2) = hdbuild l1 ⊕ hdbuild l2``,
  Induct_on `l1` >> simp[])

val allnodes_touches = store_thm(
  "allnodes_touches",
  ``(∀n. a <: nnodes n ∧ agtouches a g2 ⇒ ngtouches n g2) ∧
    (∀g1. a <: allnodes g1 ∧ agtouches a g2 ⇒ g1 ∼ᵍ g2)``,
  ho_match_mp_tac hidag_ind >> simp[] >> metis_tac[]);

val FOLDL_graphOfL_same_start = store_thm(
  "FOLDL_graphOfL_same_start",
  ``∀l m0 g0.
      FOLDL (graphOfL lf cf lab) (SOME(m0,g0)) l = SOME(m,g) ⇒
      ∃gd. g = g0 ⊕ gd ∧
           ∀g0'. FOLDL (graphOfL lf cf lab) (SOME(m0,g0')) l =
                 SOME(m,g0' ⊕ gd)``,
  Induct >> simp[] >- (qexists_tac `ε` >> simp[]) >>
  qx_genl_tac [`h`, `m0`, `g0`] >> strip_tac >>
  IMP_RES_THEN
    (qx_choosel_then [`m'`, `g'`] assume_tac)
    FOLDL_graphOfL_EQ_SOME_E >> fs[] >>
  first_x_assum (qspecl_then [`m'`, `g'`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gd1` strip_assume_tac) >>
  fs[graphOfL_def] >>
  qmatch_assum_rename_tac `graphOf (lf h lab) m0 (cf h) = SOME mg` [] >>
  `∃m0' g0'. mg = (m0', g0')` by (Cases_on `mg` >> simp[]) >> rw[] >> fs[] >>
  rw[] >> qexists_tac `HG g0' <+ ε ⊕ gd1` >> simp[hdmerge_ASSOC]);

val pcg_eval_FOLDR_nested_graphs = store_thm(
  "pcg_eval_FOLDR_nested_graphs",
  ``∀m_opt. pcg_eval (FOLDR (λg acc. HG g <+ acc) g0 l) m_opt =
            pcg_eval (MergeL l ⊕ g0) m_opt``,
  Induct_on `l` >> simp[]);

val ggentouches_FOLDR_nested_graphs = store_thm(
  "ggentouches_FOLDR_nested_graphs",
  ``FOLDR (λg acc. HG g <+ acc) g0 l ∼ᵍ g' ⇔
    g0 ∼ᵍ g' ∨ ∃g. MEM g l ∧ g ∼ᵍ g'``,
  Induct_on `l` >> simp[] >> metis_tac[]);

val MergeL_mid_to_front = store_thm(
  "MergeL_mid_to_front",
  ``(∀g'. MEM g' l1 ⇒ g' ≁ᵍ g) ⇒
    MergeL (l1 ++ [g] ++ l2) = g ⊕ MergeL (l1 ++ l2)``,
  Induct_on `l1` >> simp[] >> dsimp[] >>
  metis_tac[hdmerge_ASSOC, hdmerge_COMM]);

val destDValue_Value_COND = store_thm(
  "destDValue_Value_COND",
  ``destDValue (DValue v) = if isArrayError v then Error
                            else v``,
  Cases_on `v` >> simp[]);

val graphOf_correct_lemma = store_thm(
  "graphOf_correct_lemma",
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      ∀i0 m0' g0.
        graphOf i0 m0 c0 = SOME (m0', g0) ⇒
        ∃g.
          graphOf i0 m c = SOME(m0', g) ∧
          ∀g'. g ∼ᵍ g' ⇒ g0 ∼ᵍ g'``,
  ho_match_mp_tac eval_ind' >> rpt conj_tac >>
  TRY (simp[graphOf_def] >> NO_TAC)
  >- ((* seq head takes one step *)
      simp[graphOf_def', PULL_EXISTS, FORALL_PROD, EXISTS_PROD,
           FOLDL_APPEND] >>
      qx_genl_tac [`c`, `c0`, `pfx`, `sfx`, `m0`, `m`] >> strip_tac >>
      qabbrev_tac
        `empties = GENLIST (K (HG ε <+ ε)) (LENGTH pfx) : value list pcg list`>>
      `∀m l. FOLDL (graphOfL (K I) I l) (SOME(m,ε)) pfx = SOME (m, MergeL empties)`
        by (Q.UNDISCH_THEN `EVERY ((=) Done) pfx` mp_tac >>
            simp[Abbr`empties`] >>
            qabbrev_tac `p' = REVERSE pfx` >>
            `LENGTH pfx = LENGTH p' ∧
             EVERY ((=) Done) pfx = EVERY ((=) Done) p'`
              by simp[Abbr`p'`, EVERY_MEM] >>
            simp[FOLDL_FOLDR_REVERSE] >> ntac 3 (pop_assum kall_tac) >>
            qid_spec_tac `p'` >> Induct >> simp[GENLIST_CONS] >>
            simp[graphOfL_def, Once hdmerge_COMM]) >>
      simp[graphOfL_def] >>
      qx_genl_tac [`lab0`, `m1`, `g1`] >> strip_tac >>
      IMP_RES_THEN mp_tac FOLDL_graphOfL_EQ_SOME_E >> simp[EXISTS_PROD] >>
      disch_then (qx_choosel_then [`m01`, `g01`] assume_tac) >> fs[] >>
      `∃g01'. graphOf lab0 m c = SOME(m01,g01') ∧ ∀g'. g01' ∼ᵍ g' ⇒ g01 ∼ᵍ g'`
        by metis_tac[] >>
      simp[] >> imp_res_tac FOLDL_graphOfL_same_start >> simp[] >> metis_tac[])
  >- ((* seq is all Dones *)
      qx_gen_tac `m0` >> simp[graphOf_def'] >> qx_gen_tac `cs` >>
      simp[FOLDL_FOLDR_REVERSE] >>
      qabbrev_tac `cs' = REVERSE cs` >>
      `EVERY ($= Done) cs ⇔ EVERY ($= Done) cs'` by simp[EVERY_MEM, Abbr`cs'`] >>
      pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >> Induct_on `cs'` >>
      simp[] >> simp[Once graphOfL_def, PULL_EXISTS, FORALL_PROD] >> metis_tac[])
  >- ((* seq includes an abort *) simp[graphOf_def'] >>
      `∀pfx sfx lab mgopt.
         FOLDL (graphOfL (K I) I lab) mgopt (pfx ++ [Abort] ++ sfx) = NONE`
        suffices_by simp[] >>
      Induct_on `pfx` >> simp[graphOf_def, graphOfL_def] >>
      rpt gen_tac >>
      `mgopt = NONE ∨ ∃m g. mgopt = SOME (m,g)`
        by metis_tac[option_CASES, pair_CASES] >>
      simp[])
  >- ((* guard of if evaluates to boolean and next statement selected *)
      map_every qx_gen_tac [`m0`, `gd`, `t`, `e`, `b`] >>
      rpt gen_tac >> strip_tac >> simp[graphOf_def, PULL_EXISTS, EXISTS_PROD] >>
      Cases_on `b` >> simp[EXISTS_PROD, PULL_EXISTS, FORALL_PROD])
  >- ((* guard of if evaluates to non-boolean (type error) *)
      rpt gen_tac >> strip_tac >> simp[graphOf_def] >>
      Cases_on `evalexpr m0 g` >> simp[] >> fs[])
  >- ((* assignment to array completes *)
      simp[graphOf_def, PULL_EXISTS, evalexpr_def, OPT_SEQUENCE_EQ_SOME,
           MEM_MAP, isDValue_destDValue])
  >- ((* assignment to array fails at upd_array stage *)
      simp[graphOf_def, PULL_EXISTS, evalexpr_def, OPT_SEQUENCE_EQ_SOME,
           MEM_MAP, isDValue_destDValue])
  >- ((* data-read inside assignment *)
      qx_genl_tac [`pfx`, `e`, `sfx`, `w`, `vf`, `m0`, `i0`, `m`, `g`] >>
      simp[graphOf_def, OPT_SEQUENCE_EQ_SOME, MEM_MAP, evalDexpr_def,
           evalexpr_def, PULL_EXISTS] >>
      simp[getReads_APPEND, getReads_def, PULL_EXISTS] >>
      qx_genl_tac [`lv`, `sfx_rds`, `pfx_rds`, `erd`] >> strip_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, value_case_eq] >>
      `¬isArrayError (evalmaccess m0 e)`
        by (Cases_on `evalmaccess m0 e` >> fs[]) >> fs[] >> conj_tac
      >- (Cases_on `evalmaccess m0 e` >> fs[]) >>
      veq >>
      simp[gentouches_def, dvreadAction_def, mareadAction_def, dvread_def,
           PULL_EXISTS] >>
      rpt strip_tac >> simp[] >> metis_tac[])
  >- ((* data-read list now includes an Array or Error *)
      dsimp[graphOf_def, OPT_SEQUENCE_EQ_SOME, evalDexpr_def, MEM_MAP])
  >- ((* forloop turns into seq *)
      simp[graphOf_def', EXISTS_PROD, PULL_EXISTS, FOLDL_MAP] >>
      `∀i0 x vnm body.
         (λdv. graphOfL (K I) I i0 x (Label dv (ssubst vnm dv body))) =
         graphOfL CONS (λdv. ssubst vnm dv body) i0 x`
        by simp[graphOfL_def, FUN_EQ_THM] >>
      asm_simp_tac (srw_ss() ++ ETA_ss) [])
  >- ((* parloop turns into par *)
      simp[graphOf_def', MAP_MAP_o, combinTheory.o_ABS_R, oneTheory.one,
           PULL_EXISTS])
  >- ((* one component of a par takes a step *)
      map_every qx_gen_tac [`m0`, `m`, `pfx`, `c0`, `c`, `sfx`] >>
      strip_tac >>
      simp[graphOf_def, oneTheory.one, PULL_EXISTS, OPT_SEQUENCE_EQ_SOME,
           MAP_MAP_o, combinTheory.o_ABS_R] >>
      qabbrev_tac `
        TOS = λi m c. THE (OPTION_MAP SND (graphOf i m c))` >> simp[] >>
      qx_genl_tac [`i0`, `m00`] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, MEM_MAP] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      qx_genl_tac [`m0'`, `g0'`] >> strip_tac >>
      `∃g'. graphOf i0 m c = SOME(m0',g') ∧
            ∀g2. g' ∼ᵍ g2 ⇒ g0' ∼ᵍ g2` by metis_tac[] >>
      simp[] >>
      `∀d. MEM d pfx ⇒
           (∃dm. graphOf i0 m d = SOME(dm, TOS i0 m0 d)) ∧
           TOS i0 m d = TOS i0 m0 d`
        by (Cases_on `m0 = m` >> simp[]
            >- (simp[Abbr`TOS`] >> rpt strip_tac >> res_tac >>
                simp[] >> rw[]) >>
            `∃a. BAG_IN a (allnodes g0') ∧
                 apply_action (polydata_upd SND a) (SOME m0) = SOME m`
              by metis_tac[eval_graphOf_action] >>
            qx_gen_tac `d` >> strip_tac >>
            `∃dm dg. graphOf i0 m0 d = SOME(dm,dg)` by metis_tac[] >>
            `¬agtouches (polydata_upd SND a) dg`
              by (simp[] >> strip_tac >>
                  `dg ∼ᵍ g0'` by metis_tac[allnodes_touches, gentouches_SYM] >>
                  `∃di. di < LENGTH pfx ∧ d = EL di pfx` by metis_tac[MEM_EL] >>
                  first_x_assum (qspecl_then [`di`, `LENGTH pfx`] mp_tac) >>
                  simp[EL_APPEND1, EL_APPEND2, EL_MAP] >>
                  simp[Abbr`TOS`] >> rw[]) >>
            `∃dm'. graphOf i0 m d = SOME(dm', dg)`
              by metis_tac[graphOf_apply_action_diamond] >>
            simp[Abbr`TOS`]) >>
      pop_assum (strip_assume_tac o
                 SIMP_RULE (srw_ss()) [IMP_CONJ_THM, FORALL_AND_THM,
                                       GSYM RIGHT_EXISTS_IMP_THM,
                                       SKOLEM_THM]) >>
      `∀d. MEM d sfx ⇒
           (∃dm. graphOf i0 m d = SOME(dm, TOS i0 m0 d)) ∧
           TOS i0 m d = TOS i0 m0 d`
        by (Cases_on `m0 = m` >> simp[]
            >- (simp[Abbr`TOS`] >> rpt strip_tac >> res_tac >>
                simp[] >> rw[]) >>
            `∃a. BAG_IN a (allnodes g0') ∧
                 apply_action (polydata_upd SND a) (SOME m0) = SOME m`
              by metis_tac[eval_graphOf_action] >>
            qx_gen_tac `d` >> strip_tac >>
            `∃dm dg. graphOf i0 m0 d = SOME(dm,dg)` by metis_tac[] >>
            `¬agtouches (polydata_upd SND a) dg`
              by (simp[] >> strip_tac >>
                  `dg ∼ᵍ g0'` by metis_tac[allnodes_touches, gentouches_SYM] >>
                  `∃di. di < LENGTH sfx ∧ d = EL di sfx` by metis_tac[MEM_EL] >>
                  first_x_assum
                    (qspecl_then [`LENGTH pfx`, `LENGTH pfx + 1 + di`] mp_tac) >>
                  simp[EL_APPEND1, EL_APPEND2, EL_MAP] >>
                  simp[Abbr`TOS`] >> rw[] >> metis_tac[gentouches_SYM]) >>
            `∃dm'. graphOf i0 m d = SOME(dm', dg)`
              by metis_tac[graphOf_apply_action_diamond] >>
            simp[Abbr`TOS`]) >>
      pop_assum (strip_assume_tac o
                 SIMP_RULE (srw_ss()) [IMP_CONJ_THM, FORALL_AND_THM,
                                       GSYM RIGHT_EXISTS_IMP_THM,
                                       SKOLEM_THM]) >>
      simp[Cong (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO] MAP_CONG)] >>
      rpt conj_tac
      >- (qx_genl_tac [`i`, `j`] >> strip_tac >>
          first_x_assum (qspecl_then [`i`, `j`] mp_tac) >> simp[] >>
          Cases_on `j < LENGTH pfx` >- (simp[EL_APPEND1]) >>
          Cases_on `j = LENGTH pfx`
          >- (simp[EL_APPEND1, EL_APPEND2] >>
              simp[Abbr`TOS`] >> metis_tac[gentouches_SYM]) >>
          Cases_on `i < LENGTH pfx` >- simp[EL_APPEND1, EL_APPEND2] >>
          Cases_on `i = LENGTH pfx`
          >- (simp[EL_APPEND1, EL_APPEND2] >> simp[Abbr`TOS`] >>
              metis_tac[]) >>
          simp[EL_APPEND2, EL_APPEND1])
      >- (fs[pcg_eval_FOLDR_nested_graphs] >>
          `∀g0. MEM g0 (MAP (λc. TOS i0 m0 c) pfx) ⇒ g0 ≁ᵍ TOS i0 m0 c0`
            by (dsimp[MEM_MAP] >> qx_gen_tac `p` >> strip_tac >>
                `∃p_i. p_i < LENGTH pfx ∧ p = EL p_i pfx`
                  by metis_tac[MEM_EL] >>
                first_x_assum (qspecl_then [`p_i`, `LENGTH pfx`] mp_tac) >>
                simp[EL_APPEND1, EL_APPEND2, EL_MAP]) >>
          fs[MergeL_mid_to_front] >>
          `∀g0. MEM g0 (MAP (λc. TOS i0 m0 c) pfx) ⇒ g0 ≁ᵍ TOS i0 m c`
            by (simp[Abbr`TOS`] >> pop_assum mp_tac >> simp[] >>
                metis_tac[gentouches_SYM]) >>
          simp[MergeL_mid_to_front] >>
          `pcg_eval (TOS i0 m c) (SOME m) = pcg_eval (TOS i0 m0 c0) (SOME m0)`
            suffices_by simp[] >>
          simp[Abbr`TOS`] >> metis_tac[graphOf_pcg_eval]) >>
      simp[ggentouches_FOLDR_nested_graphs] >>
      dsimp[MEM_MAP] >> rpt strip_tac
      >- metis_tac[]
      >- (pop_assum mp_tac >> simp[Abbr`TOS`])
      >- metis_tac[])
  >- ((* par is all Dones component *)
      simp[graphOf_def, PULL_EXISTS, OPT_SEQUENCE_EQ_SOME,
           combinTheory.o_ABS_L, combinTheory.o_ABS_R,
           MEM_MAP, MAP_MAP_o, EL_MAP, pcg_eval_FOLDR_nested_graphs] >>
      qx_genl_tac [`m0`, `cs`] >> strip_tac >>
      `∀n. n < LENGTH cs ⇒ EL n cs = Done` by fs[EVERY_EL] >>
      simp[graphOf_def] >>
      `∀i m c. MEM c cs ⇒ graphOf i m c = SOME(m,ε)`
        by (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
            rw[]) >>
      simp[Cong (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO] MAP_CONG)] >>
      `MergeL (MAP (λc. ε) cs) = ε : value list pcg` suffices_by simp[] >>
      match_mp_tac MergeL_empties >> simp[MEM_MAP, PULL_EXISTS])
  >- ((* Par contains an abort *)
      simp[graphOf_def, OPT_SEQUENCE_EQ_SOME, MEM_MAP,
           PULL_EXISTS] >> rpt strip_tac >>
      disj1_tac >> qexists_tac `Abort` >> simp[])
  >- ((* Local *) simp[graphOf_def, PULL_EXISTS, EXISTS_PROD])
);

val graphOf_correct0 = prove(
  ``∀p1 p2.
      p1 --->* p2 ⇒
      ∀m0 c0 m i0 i g gm.
        p1 = (m0,c0) ∧ p2 = (m,Done) ∧
        graphOf i0 m0 c0 = SOME(gm,g) ⇒
        gm = m``,
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  simp[FORALL_PROD] >> metis_tac[graphOf_correct_lemma]);

val graphOf_determines_evaluation = save_thm(
  "graphOf_determines_evaluation",
  graphOf_correct0 |> SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO])

val RTC_RULE2 = RTC_RULES |> SPEC_ALL |> CONJUNCT2

val eval_seq_sing = store_thm(
  "eval_seq_sing[simp]",
  ``(m0, Seq [c]) --->* (m, Done) ⇔ (m0, c) --->* (m, Done)``,
  eq_tac
  >- (`∀mr0 mr. mr0 --->* mr ⇒
                ∀m0 c m. mr0 = (m0, Seq [c]) ∧ mr = (m, Done) ⇒
                       (m0, c) --->* (m, Done)`
        suffices_by metis_tac[] >>
      ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> dsimp[] >>
      simp[Once eval_cases, FORALL_PROD] >>
      dsimp[APPEND_EQ_CONS] >> metis_tac[RTC_RULES]) >>
  `∀mr0 mr. mr0 --->* mr ⇒
            ∀m0 c m. mr0 = (m0, c) ∧ mr = (m, Done) ⇒
                     (m0, Seq [c]) --->* (m, Done)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >> dsimp[] >> conj_tac
  >- (gen_tac >> match_mp_tac RTC_SUBSET >> simp[Once eval_cases]) >>
  simp[FORALL_PROD] >> qx_genl_tac [`m'`, `c'`, `m0`, `c`, `m`] >>
  strip_tac >> match_mp_tac RTC_RULE2 >>
  qexists_tac `(m', Seq [c'])` >> simp[] >>
  simp[Once eval_cases] >> dsimp[APPEND_EQ_CONS]);

val bb = prove(``(!b. b) = F``, SIMP_TAC bool_ss [FORALL_BOOL])

val graphOf_ind = theorem "graphOf_ind"

val graphOf_ind' = save_thm(
  "graphOf_ind'",
    WF_INDUCTION_THM
      |> Q.ISPEC `inv_image (mlt (<) LEX (<))
                            (λs. (loopbag s, stmt_weight (K 0) s))`
      |> SIMP_RULE (srw_ss()) [WF_mlt1, WF_inv_image, pairTheory.WF_LEX,
                               WF_TC])

val assign_evalDexpr_lemma = prove(
  ``∀ds rvs m.
       OPT_SEQUENCE (MAP (evalDexpr m) ds) = SOME rvs ⇒
       (m, Assign lve ds f) --->* (m, Assign lve (MAP DValue rvs) f)``,
  simp[OPT_SEQUENCE_EQ_SOME, MEM_MAP, PULL_EXISTS] >>
  Induct_on `LENGTH (FILTER ($~ o isDValue) ds)` >>
  simp[LENGTH_NIL_SYM, FILTER_EQ_NIL]
  >- (rpt strip_tac >>
      `MAP DValue (MAP THE (MAP (evalDexpr m) ds)) = ds`
        suffices_by simp[] >>
      fs[EVERY_MEM] >> simp[LIST_EQ_REWRITE, EL_MAP] >>
      qx_gen_tac `i` >> strip_tac >>
      `isDValue (EL i ds) ∧ ∃v. evalDexpr m (EL i ds) = SOME v`
        by metis_tac[MEM_EL] >>
      Cases_on `EL i ds` >> fs[] >> fs[evalDexpr_def]) >>
  dsimp[LENGTH_CONS, FILTER_EQ_CONS, FILTER_EQ_NIL] >>
  rpt strip_tac >>
  qmatch_assum_rename_tac `LENGTH (FILTER ($~ o isDValue) sfx) = n` [] >>
  qmatch_assum_rename_tac `EVERY (λx. isDValue x) pfx` [] >>
  qmatch_assum_rename_tac `evalDexpr m rd = SOME v` [] >>
  `∃ma. rd = DMA ma` by (Cases_on `rd` >> fs[evalDexpr_def]) >> veq >> fs[] >>
  match_mp_tac RTC_RULE2 >>
  qexists_tac `(m, Assign lve (pfx ++ [DValue v] ++ sfx) f)` >> conj_tac
  >- (simp[Once eval_cases] >>
      `evalmaccess m ma = v` suffices_by metis_tac[] >>
      fs[evalDexpr_def, value_case_eq]) >>
  first_x_assum (qspec_then `pfx ++ [DValue v] ++ sfx` mp_tac) >>
  simp[FILTER_APPEND_DISTRIB] >>
  `¬isArrayError v` by (fs[evalDexpr_def, value_case_eq] >> rw[]) >>
  `LENGTH (FILTER ($~ o isDValue) pfx) = 0`
    by simp[LENGTH_NIL, FILTER_EQ_NIL] >>
  dsimp[evalDexpr_def])

val graphOf_implies_Done_computation = store_thm(
  "graphOf_implies_Done_computation",
  ``∀c0 lab m0 m g. graphOf lab m0 c0 = SOME (m, g) ⇒ (m0,c0) --->* (m, Done)``,
  ho_match_mp_tac graphOf_ind' >> simp[] >> Cases >> simp[] >>
  TRY (simp[graphOf_def] >> NO_TAC)
  >- ((* assign *) simp[graphOf_def, PULL_EXISTS] >>
      disch_then kall_tac >> rpt strip_tac >>
      qmatch_assum_rename_tac `eval_lvalue m0 lve = SOME lv` [] >>
      qmatch_assum_rename_tac `getReads m0 ds = SOME rds` [] >>
      qmatch_rename_tac `(m0, Assign lve ds f) --->* (m,Done)` [] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0, Assign lve (MAP DValue rvs) f)` >> conj_tac
      >- metis_tac[assign_evalDexpr_lemma] >>
      match_mp_tac RTC_SUBSET >>
      simp[Once eval_cases, EVERY_MEM, MEM_MAP, PULL_EXISTS, MAP_MAP_o] >>
      imp_res_tac evalDexpr_notArrayError >> simp[] >>
      `MAP (destDValue o DValue) rvs = rvs` suffices_by simp[] >>
      simp[LIST_EQ_REWRITE, EL_MAP, destDValue_Value_COND] >> rw[] >>
      metis_tac[MEM_EL])
  >- ((* if *) simp[graphOf_def, value_case_eq, bool_case_eq, EXISTS_PROD] >>
      dsimp[] >> rpt strip_tac >> match_mp_tac RTC_RULE2 >>
      simp[EXISTS_PROD, Once eval_cases, bb] >>
      fs[AND_IMP_INTRO] >> first_x_assum match_mp_tac >>
      simp[pairTheory.LEX_DEF, MAX_PLUS] >> metis_tac[])
  >- ((* forloop *)
      simp[graphOf_def', PULL_EXISTS, FORALL_PROD] >> strip_tac >>
      qx_genl_tac [`lab`, `m0`, `m`, `dvs`, `g`] >> strip_tac >>
      match_mp_tac RTC_RULE2 >>
      simp[Once eval_cases, EXISTS_PROD] >>
      Q.UNDISCH_THEN `dvalues m0 d = SOME dvs` kall_tac >>
      qabbrev_tac `g0 : value list pcg = ε` >>
      Q.RM_ABBREV_TAC `g0` >>
      pop_assum mp_tac >> map_every qid_spec_tac [`m0`, `g0`] >>
      Induct_on `dvs` >> simp[]
      >- (match_mp_tac RTC_RULE2 >> simp[EXISTS_PROD, Once eval_cases]) >>
      qx_gen_tac `d0` >> dsimp[] >> qx_genl_tac [`g0`, `m0`] >>
      disch_then (fn th =>
        assume_tac th >>
        strip_assume_tac (MATCH_MP FOLDL_graphOfL_EQ_SOME_E th)) >> fs[] >>
      pop_assum mp_tac >>
      dsimp[graphOfL_def, FORALL_PROD] >> qx_gen_tac `subg` >> strip_tac >>
      qmatch_assum_rename_tac
        `graphOf (d0::lab) m0 (ssubst vnm d0 body) = SOME (m0', subg)` [] >>
      qabbrev_tac `bod' = ssubst vnm d0 body` >>
      `(m0, bod') --->* (m0', Done)`
        by (fs[AND_IMP_INTRO, PULL_FORALL] >> first_x_assum match_mp_tac >>
            simp[Abbr`bod'`, pairTheory.LEX_DEF] >> rw[] >> metis_tac[]) >>
      `(m0, Label d0 bod') --->* (m0', Done)`
        by (`(m0, Label d0 bod') --->* (m0', Label d0 Done)` by simp[] >>
            `(m0', Label d0 Done) ---> (m0', Done)` by simp[Once eval_cases] >>
            metis_tac[RTC_CASES2]) >>
      qmatch_abbrev_tac `(m0, Seq (Label d0 bod' :: rest)) --->* (m, Done)` >>
      `(m0, Seq (Label d0 bod' :: rest)) --->* (m0', Seq (Done :: rest))`
        by simp[evalrtc_seq |> Q.INST [`pfx` |-> `[]`]
                            |> SIMP_RULE (srw_ss()) []] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0',Seq (Done :: rest))` >> simp[] >>
      first_x_assum match_mp_tac >> qexists_tac `g0'` >> simp[])
  >- ((* parloop *) simp[graphOf_def', PULL_EXISTS] >> strip_tac >>
      qx_genl_tac [`lab`, `m0`, `m`, `dvs`, `gs`] >> strip_tac >>
      match_mp_tac RTC_RULE2 >> simp[EXISTS_PROD, Once eval_cases] >> fs[] >>
      Q.UNDISCH_THEN `dvalues m0 d = SOME dvs` kall_tac >>
      ntac 3 (pop_assum mp_tac) >> map_every qid_spec_tac [`gs`, `m0`] >>
      Induct_on `dvs` >> simp[]
      >- (simp[OPT_SEQUENCE_def] >> rw[] >>
          match_mp_tac RTC_RULE2 >> simp[EXISTS_PROD, Once eval_cases]) >>
      dsimp[OPT_SEQUENCE_def, PULL_EXISTS, FORALL_PROD] >>
      qx_genl_tac [`dv`, `m0`, `gs0`, `m'`, `g'`] >> rpt strip_tac >>
      `∀i j. i < j ∧ j < LENGTH gs0 ⇒ EL i gs0 ≁ᵍ EL j gs0`
        by (rpt gen_tac >>
            first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
            simp[]) >>
      `pcg_eval g' (SOME m0) = SOME m'` by metis_tac[graphOf_pcg_eval] >>
      first_x_assum (qspecl_then [`m'`, `gs0`] mp_tac) >> simp[] >> fs[] >>
      qmatch_assum_rename_tac
        `graphOf (dv::lab) m0 (ssubst vnm dv body) = SOME (m', g')` [] >>
      fs[AND_IMP_INTRO, PULL_FORALL] >>
      `(m0, ssubst vnm dv body) --->* (m', Done)`
        by (first_x_assum match_mp_tac >> simp[pairTheory.LEX_DEF] >> rw[] >>
            metis_tac[]) >>
      `(m0, Label dv (ssubst vnm dv body)) --->* (m', Label dv Done)`
        by simp[] >>
      `(m', Label dv Done) --->* (m', Done)` by simp[] >>
      `(m0, Label dv (ssubst vnm dv body)) --->* (m', Done)`
        by metis_tac[RTC_CASES_RTC_TWICE] >>
      strip_tac >>
      qmatch_abbrev_tac `(m0, Par (c1 :: rest)) --->* (m, Done)` >>
      `(m0, Par (c1::rest)) --->* (m', Par (Done::rest))`
        by metis_tac[evalrtc_par |> Q.INST [`pfx` |-> `[]`]
                                 |> SIMP_RULE (srw_ss()) []] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m', Par (Done::rest))` >> simp[] >>
      match_mp_tac ParRTCDone_I >> first_x_assum match_mp_tac >>
      `MAP (λv. OPTION_MAP SND (graphOf (v::lab) m' (ssubst vnm v body)))
           dvs =
       MAP (λv. OPTION_MAP SND (graphOf (v::lab) m0 (ssubst vnm v body)))
           dvs` suffices_by simp[] >>
      simp[MAP_EQ_f] >> qx_gen_tac `dv'` >> strip_tac >>
      fs[OPT_SEQUENCE_EQ_SOME, MEM_MAP, PULL_EXISTS] >>
      first_x_assum (qspec_then `dv'` mp_tac) >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      `∃dvi'. dvi' < LENGTH dvs ∧ dv' = EL dvi' dvs` by metis_tac[MEM_EL] >>
      qx_genl_tac [`m''`, `g''`] >>
      Q.SUBGOAL_THEN `0 < SUC dvi' ∧ SUC dvi' < SUC (LENGTH gs0)`
        (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >> simp[EL_MAP] >>
      csimp[AND_IMP_INTRO] >>
      metis_tac[graphOf_pcg_eval_diamond])
  >- ((* seq *) simp[graphOf_def', PULL_EXISTS, FORALL_PROD] >> strip_tac >>
      qx_genl_tac [`lab`, `m0`, `m`, `g`] >> strip_tac >>
      qabbrev_tac `g0 : value list pcg = ε` >>
      Q.RM_ABBREV_TAC `g0` >>
      qmatch_rename_tac `(m0, Seq cs) --->* (m, Done)` [] >>
      `∀c lab m0 m g.
          MEM c cs ∧ graphOf lab m0 c = SOME(m,g) ⇒ (m0,c) --->* (m,Done)`
        by (rpt strip_tac >> fs[AND_IMP_INTRO, PULL_FORALL] >>
            first_x_assum match_mp_tac >> simp[pairTheory.LEX_DEF] >>
            imp_res_tac (MEM_FOLDR_mlt |> INST_TYPE [alpha |-> ``:stmt``]
                                       |> Q.INST [`f` |-> `I`]
                                       |> SIMP_RULE (srw_ss()) []
                                       |> GEN_ALL) >>
            simp[] >> asm_simp_tac (srw_ss() ++ ETA_ss) [SUM_MAP_lemma] >>
            metis_tac[]) >>
      ntac 2 (pop_assum mp_tac) >> pop_assum kall_tac >>
      map_every qid_spec_tac [`m0`, `g0`] >>
      Induct_on `cs` >> simp[]
      >- (match_mp_tac RTC_RULE2 >>
          simp[EXISTS_PROD, Once eval_cases]) >>
      qx_gen_tac `c0` >> dsimp[] >> qx_genl_tac [`g0`, `m0`] >>
      disch_then (fn th =>
        assume_tac th >>
        strip_assume_tac (MATCH_MP FOLDL_graphOfL_EQ_SOME_E th)) >> fs[] >>
      pop_assum mp_tac >>
      dsimp[graphOfL_def, FORALL_PROD] >> qx_gen_tac `subg` >> rpt strip_tac >>
      `(m0, c0) --->* (m0', Done)` by metis_tac[] >>
      `(m0, Seq (c0 :: cs)) --->* (m0', Seq (Done :: cs))`
        by simp[evalrtc_seq |> Q.INST [`pfx` |-> `[]`]
                            |> SIMP_RULE (srw_ss()) []] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0',Seq (Done :: cs))` >> simp[] >>
      first_x_assum (qspecl_then [`g0'`, `m0'`] mp_tac) >> simp[] >>
      disch_then match_mp_tac >> metis_tac[])
  >- ((* par *) simp[graphOf_def', PULL_EXISTS] >>
      rpt strip_tac >> qmatch_rename_tac `(m0, Par cs) --->* (m, Done)` [] >>
      `∀c lab m0 m g.
        MEM c cs ∧ graphOf lab m0 c = SOME(m,g) ⇒ (m0,c) --->* (m,Done)`
        by (rpt strip_tac >> fs[AND_IMP_INTRO, PULL_FORALL] >>
            first_x_assum match_mp_tac >> simp[pairTheory.LEX_DEF] >>
            imp_res_tac (MEM_FOLDR_mlt |> INST_TYPE [alpha |-> ``:stmt``]
                                       |> Q.INST [`f` |-> `I`]
                                       |> SIMP_RULE (srw_ss()) []
                                       |> GEN_ALL) >>
            simp[] >> asm_simp_tac (srw_ss() ++ ETA_ss) [SUM_MAP_lemma] >>
            metis_tac[]) >>
      ntac 4 (pop_assum mp_tac) >> pop_assum kall_tac >>
      map_every qid_spec_tac [`m0`, `gs`] >>
      Induct_on `cs` >> dsimp[OPT_SEQUENCE_def, PULL_EXISTS, FORALL_PROD]
      >- simp[Once eval_cases] >>
      qx_genl_tac [`c`, `m0`, `gs`, `m0'`, `g0'`] >> rpt strip_tac >> fs[] >>
      simp[Once RTC_CASES_RTC_TWICE] >>
      qexists_tac `(m0', Par(Done::cs))` >> simp[] >> conj_tac
      >- (match_mp_tac (evalrtc_par |> Q.INST [`pfx` |-> `[]`]
                                    |> SIMP_RULE (srw_ss()) []) >>
          metis_tac[]) >>
      match_mp_tac ParRTCDone_I >> fs[AND_IMP_INTRO] >>
      first_x_assum (qspecl_then [`gs`, `m0'`] match_mp_tac) >> simp[] >>
      rpt conj_tac
      >- (`MAP (λc. OPTION_MAP SND (graphOf lab m0' c)) cs =
           MAP (λc. OPTION_MAP SND (graphOf lab m0 c)) cs`
            suffices_by simp[] >>
          simp[MAP_EQ_f] >>
          fs[OPT_SEQUENCE_EQ_SOME, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
          qx_gen_tac `c'` >> strip_tac >>
          `∃m' g'. graphOf lab m0 c' = SOME(m', g')` by metis_tac[] >>
          `∃m''. graphOf lab m0' c' = SOME(m'',g')`
            suffices_by simp[PULL_EXISTS] >>
          `pcg_eval g0' (SOME m0) = SOME m0'` by metis_tac[graphOf_pcg_eval] >>
          `g0' ≁ᵍ g'` suffices_by metis_tac[graphOf_pcg_eval_diamond] >>
          `∃i. i < LENGTH cs ∧ c' = EL i cs` by metis_tac[MEM_EL] >>
          `EL i gs = g'` by rw[EL_MAP] >>
          first_x_assum (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[])
      >- (rpt strip_tac >>
          first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
          simp[])
      >- metis_tac[graphOf_pcg_eval]
      >- metis_tac[])
  >- ((* Local *) simp[graphOf_def, PULL_EXISTS, FORALL_PROD] >>
      rpt strip_tac >> match_mp_tac RTC_RULE2 >>
      simp[Once eval_cases, EXISTS_PROD] >>
      fs[isArrayError_DISJ_EQ, AND_IMP_INTRO, PULL_FORALL] >>
      first_x_assum match_mp_tac >> simp[pairTheory.LEX_DEF] >>
      metis_tac[])
  >- ((* Label *) simp[graphOf_def, PULL_EXISTS, FORALL_PROD] >>
      rpt strip_tac >> simp[Once RTC_CASES2] >>
      qmatch_assum_rename_tac `graphOf (v::lab) m0 s0 = SOME(m,g)` [] >>
      qexists_tac `(m, Label v Done)` >> reverse conj_tac
      >- simp[Once eval_cases] >>
      match_mp_tac Label_RTC_mono >> fs[AND_IMP_INTRO, PULL_FORALL] >>
      first_x_assum match_mp_tac >> simp[pairTheory.LEX_DEF] >>
      metis_tac[])
)

val graphOf_correct = store_thm(
  "graphOf_correct",
  ``∀m0 c m lab g.
       graphOf lab m0 c = SOME(m,g) ⇒
       ∀m'. (m0,c) --->* (m', Done) ⇔ m' = m``,
  metis_tac[graphOf_determines_evaluation, graphOf_implies_Done_computation]);

val _ = export_theory();
