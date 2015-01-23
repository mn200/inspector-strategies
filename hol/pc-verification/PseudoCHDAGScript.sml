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

val gentouches_touches = store_thm(
  "gentouches_touches[simp]",
  ``gentouches (set o action_reads) (set o action_write)
               (set o action_reads) (set o action_write) a1 a2 ⇔
      a1 ∼ₜ a2``,
  simp[touches_def, gentouches_def] >>
  map_every Cases_on [`a1.write`, `a2.write`] >>
  simp[] >> metis_tac[]);

(* ----------------------------------------------------------------------

    pcg_eval : α pcg -> memory option -> memory option

    The function that takes a nested/hierarchical action graph and
    evaluates its effect on a piece of memory. Because action
    application can fail, so too must this. To make the types neater,
    (and to match up with apply_action, for which similar comments
    apply) it then makes sense to allow this function is take in a
    failure state as input. This is just propagated.

    The obvious approach to defining pcg_eval would start by instantiating

       hidag_recursion
           |> INST_TYPE [gamma |-> ``:memory option -> memory option``,
                         delta |-> ``:memory option -> memory option``,
                         alpha |-> ``:actionRW``,
                         beta |-> ``:α # (value list -> value)``]
           |> Q.SPECL [`λm. m`,
                       `λn g nr gr m. gr (nr m)`, `λg gr. gr`,
                       `λa. apply_action (polydata_upd SND a)`]

    along these lines, but you are then stuck with trying to imagine what
    the reads and writes should be for functions of type

        :memory option -> memory option

    If you guess that they all have empty sets of both, then the commuting
    requirement becomes impossible to show. It's hard to imagine what else
    you could pick for the read and writes set, so an alternative approach
    is required.

    We define a function, gflat_eval, that ignores nested graphs, and just
    evaluates actions that appear at the top level. The commuting
    requirement then becomes manageable, and we can define the eventual
    function by first flattening the input graph, and then using
    gflat_eval. It turns out that this combination has the desired
    characterising equations.

   ---------------------------------------------------------------------- *)

fun firstn_conjs_under_exists n th = let
  val (v, body) = dest_exists (concl th)
  val body_th = ASSUME body
  val wanted_body = LIST_CONJ (List.take(CONJUNCTS body_th, n))
  val wanted = mk_exists(v, concl wanted_body)
  val ex_th0 = EXISTS(wanted, v) wanted_body
in
  CHOOSE(v,th) ex_th0
end

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

val graphOf_ind' = save_thm(
  "graphOf_ind'",
    WF_INDUCTION_THM
      |> Q.ISPEC `inv_image (mlt (<) LEX (<))
                            (λs. (loopbag s, stmt_weight (K 0) s))`
      |> SIMP_RULE (srw_ss()) [WF_mlt1, WF_inv_image, pairTheory.WF_LEX,
                               WF_TC])

val _ = export_theory();
