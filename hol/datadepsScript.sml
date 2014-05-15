open HolKernel Parse boolLib bossLib;
open primitivesTheory forLoopTheory pred_setTheory
open listRangeTheory
open listTheory
open lcsymtacs

open actionGraphTheory

fun fds thl = full_simp_tac (srw_ss() ++ boolSimps.DNF_ss) thl

val _ = new_theory "datadeps";

val eval_def = Define`
  eval Wf Rs vf i A =
    update A (Wf i) (vf i (MAP (λf. vsub A (f i)) Rs))
`;

val apply_action_def = Define`
  apply_action a (A:'a mvector) =
    update A a.write (a.expr (MAP (vsub A) a.reads))
`;

val nontouching_actions_commute = store_thm(
  "nontouching_actions_commute",
  ``¬touches a1 a2 ⇒
    apply_action a1 (apply_action a2 A) = apply_action a2 (apply_action a1 A)``,
  simp[touches_def, apply_action_def, vector_EQ] >> rpt strip_tac >>
  map_every qabbrev_tac [`w1 = a1.write`, `w2 = a2.write`] >>
  ONCE_REWRITE_TAC [update_sub] >> simp[] >>
  Cases_on `i = w1` >> simp[]
  >- (simp[SimpRHS, update_sub] >>
      reverse (Cases_on `w1 < vsz A`) >>
      simp[update_sub, MAP_vsub]) >>
  simp[update_sub, MAP_vsub]);

val _ = overload_on("evalG", ``genEvalG apply_action``)
val evalG_rules = genEvalG_rules |> Q.ISPEC `apply_action`

val graphs_evaluate_deterministically = store_thm(
  "graphs_evaluate_deterministically",
  ``evalG A0 G A ⇒ ∀A'. evalG A0 G A' ⇒ A' = A``,
  metis_tac [genEvalG_det, nontouching_actions_commute]);

val mkEAction_def = Define`
  mkEAction wf rfs body i =
    <| write := wf i; reads := rfs <*> [i];
       expr := body i; iter := i |>
`;

val mkEAction_11 = store_thm(
  "mkEAction_11",
  ``mkEAction wf rfs body i = mkEAction wf rfs body j ⇔ i = j``,
  simp[mkEAction_def, EQ_IMP_THM]);
val _ = export_rewrites ["mkEAction_11"]

val loop_to_graph_def = tDefine "loop_to_graph" `
  loop_to_graph (lo,hi) wf rfs body =
    if lo < hi then
      add_action (mkEAction wf rfs body lo)
                 (loop_to_graph (lo+1,hi) wf rfs body)
    else emptyG
` (WF_REL_TAC `measure (λp. SND (FST p) - FST (FST p))`)

val loop_to_graph_FOLDR = store_thm(
  "loop_to_graph_FOLDR",
  ``loop_to_graph (lo,hi) wf rfs body =
      FOLDR (add_action o mkEAction wf rfs body)
            emptyG
            [lo ..< hi]``,
  Induct_on `hi - lo` >>
  simp[Once loop_to_graph_def,listRangeLHI_EMPTY, listRangeLHI_CONS]);

val eval_apply_action = store_thm(
  "eval_apply_action",
  ``eval wf rfs body i = apply_action (mkEAction wf rfs body i)``,
  simp[eval_def, apply_action_def, FUN_EQ_THM, mkEAction_def] >>
  rpt gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> Induct_on `rfs` >>
  simp[listTheory.LIST_APPLY_DEF]);

val loop_to_graph_iterations = store_thm(
  "loop_to_graph_iterations",
  ``loop_to_graph (lo,hi) wf rfs body = G ⇒
      (∀a. a ∈ G ⇒ lo ≤ a.iter ∧ a.iter < hi) ∧
      (∀a1 a2. a1 -<G>-> a2 ⇒ a1 ∈ G ∧ a2 ∈ G)``,
  qid_spec_tac `G` >> Induct_on `hi - lo` >>
  ONCE_REWRITE_TAC [loop_to_graph_def] >- simp[] >>
  rpt gen_tac >> qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> qx_gen_tac `G` >> simp[] >>
  `∃G0. loop_to_graph (lo + 1, hi) wf rfs body = G0` by simp[] >>
  `n = hi - (lo + 1)` by decide_tac >>
  `(∀a. a ∈ G0 ⇒ lo + 1 ≤ a.iter ∧ a.iter < hi) ∧
   ∀a1 a2. a1 -<G0>-> a2 ⇒ a1 ∈ G0 ∧ a2 ∈ G0` by metis_tac[] >>
  rw[] >> fs[mkEAction_def]
  >- (res_tac >> decide_tac)
  >- decide_tac
  >- (fs[add_action_edges] >> metis_tac[])
  >- (fs[add_action_edges] >> metis_tac[]));

val mkEAction_iter = store_thm(
  "mkEAction_iter",
  ``(mkEAction wf rfs body i).iter = i``,
  simp[mkEAction_def]);
val _ = export_rewrites ["mkEAction_iter"]

val loop_to_graph_correct = store_thm(
  "loop_to_graph_correct",
  ``evalG A (loop_to_graph (lo,hi) wf rfs body)
            (FOR (lo,hi) (eval wf rfs body) A)``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- simp[Once FOR_def, Once loop_to_graph_def] >>
  rpt gen_tac >>
  qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> qx_gen_tac `A` >>
  simp[Once FOR_def, Once loop_to_graph_def, eval_apply_action] >>
  match_mp_tac (CONJUNCT2 evalG_rules) >>
  `∃G. loop_to_graph (lo + 1, hi) wf rfs body = G` by simp[] >>
  simp[IN_add_action, add_action_edges] >>
  `lo ∉ iterations G`
    by (simp[iterations_thm] >> qx_gen_tac `a` >>
        Cases_on `a ∈ G` >> simp[] >>
        `lo + 1 ≤ a.iter` by metis_tac[loop_to_graph_iterations] >>
        decide_tac) >>
  `mkEAction wf rfs body lo ∉ G`
    by (strip_tac >>
        Q.UNDISCH_THEN `lo ∉ iterations G` MP_TAC >> simp[] >>
        simp[iterations_thm] >> qexists_tac `mkEAction wf rfs body lo` >>
        simp[]) >>
  simp[] >>
  qexists_tac `mkEAction wf rfs body lo` >>
  simp[] >> csimp[] >>
  qabbrev_tac `ACT = mkEAction wf rfs body lo` >> dsimp[] >>
  conj_tac >- metis_tac[IN_edges] >>
  qmatch_abbrev_tac `
    evalG AA GG (FOR (lo + 1, hi) (eval wf rfs body) AA)
  ` >>
  `n = hi - (lo + 1)` by decide_tac >>
  `GG = G` suffices_by metis_tac[] >>
  qunabbrev_tac `GG` >>
  csimp[graph_equality, add_action_edges] >> (conj_tac >- metis_tac[]) >>
  metis_tac[IN_edges]);

val apply_action_ignores_iter = store_thm(
  "apply_action_ignores_iter",
  ``apply_action (a with iter updated_by f) A = apply_action a A``,
  simp[apply_action_def]);
val _ = export_rewrites ["apply_action_ignores_iter"]

val imap_irrelevance = save_thm(
  "imap_irrelevance",
  genEvalG_imap_irrelevance
    |> C MATCH_MP (apply_action_ignores_iter |> Q.GENL [`A`, `f`, `a`]))

val INJ_COMPOSE' = prove(
  ``¬INJ f s UNIV ⇒ ¬INJ (g o f) s UNIV``,
  simp[INJ_THM] >> metis_tac[]);

val ddepR_def = Define`
  ddepR wf rfs i0 i ⇔
    i0 < i ∧ (wf i0 = wf i ∨
              MEM (wf i0) (rfs <*> [i]) ∨
              MEM (wf i) (rfs <*> [i0]))
`;

val ddepR_irreflexive = store_thm(
  "ddepR_irreflexive",
  ``∀i. ¬ddepR wf rfs i i``,
  rw[ddepR_def]);
val _ = export_rewrites ["ddepR_irreflexive"]

val ddepR_TC_LT = store_thm(
  "ddepR_TC_LT",
  ``∀i j. (ddepR wf rfs)⁺ i j ⇒ i < j``,
  ho_match_mp_tac relationTheory.TC_INDUCT >>
  rw[ddepR_def] >> decide_tac);

val ddepR_acyclic = store_thm(
  "ddepR_acyclic",
  ``∀i. ¬(ddepR wf rfs)⁺ i i``,
  rpt strip_tac >> imp_res_tac ddepR_TC_LT >> fs[]);
val _ = export_rewrites ["ddepR_acyclic"]

val vsz_eval = store_thm(
  "vsz_eval",
  ``vsz (eval wf rfs body i A) = vsz A``,
  simp[eval_def]);
val _ = export_rewrites ["vsz_eval"]

val vsz_eval_FOR = store_thm(
  "vsz_eval_FOR",
  ``vsz (FOR (lo,hi) (eval wf rfs body) A) = vsz A``,
  DEEP_INTRO_TAC FOR_RULE >> qexists_tac `λi A'. vsz A' = vsz A` >>
  simp[]);
val _ = export_rewrites ["vsz_eval_FOR"]

val vsub_eval_out_range_FOR = store_thm(
  "vsub_eval_out_range_FOR",
  ``(∀j. lo ≤ j ∧ j < hi ⇒ wf j ≠ i) ⇒ FOR (lo,hi) (eval wf rfs body) A ' i = A ' i``,
  strip_tac >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λj a. a ' i = A ' i` >> simp[eval_def] >>
  simp[update_sub]);

val FOLDR_MAP_o = store_thm(
  "FOLDR_MAP_o",
  ``!l a. FOLDR f a (MAP g l) = FOLDR (f o g) a l``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val FOLDL_MAP_combins = store_thm(
  "FOLDL_MAP_combins",
  ``!l a. FOLDL f a (MAP g l) = FOLDL (combin$C ((o) o f) g) a l``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val mkEAction_o = store_thm(
  "mkEAction_o",
  ``mkEAction wf rfs body o f =
    iter_fupd f o mkEAction (wf o f) (MAP (\rf. rf o f) rfs) (body o f)``,
  simp[FUN_EQ_THM, mkEAction_def, SINGL_APPLY_PERMUTE, MAP_MAP_o,
       combinTheory.o_ABS_R, SINGL_APPLY_MAP]);



val ALL_DISTINCT_MAP_INJ = store_thm(
  "ALL_DISTINCT_MAP_INJ",
  ``(!x y. MEM x l ∧ MEM y l ==> ((f x = f y) <=> (x = y))) ⇒
    (ALL_DISTINCT (MAP f l) <=> ALL_DISTINCT l)``,
  Induct_on `l` THEN ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP] THEN
  METIS_TAC[]);

val same_graphs = store_thm(
  "same_graphs",
  ``(∀i0 i. i < N ∧ ddepR wf rds i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N) ⇒
    loop_to_graph (0,N) (wf o γ) (MAP (λf. f o γ) rds) (body o γ) =
      imap δ (loop_to_graph (0,N) wf rds body)``,
  strip_tac >> pop_assum (assume_tac o SYM) >>
  `∀n. n < N ⇒ γ (δ n) = n ∧ δ (γ n) = n`
     by metis_tac[IN_COUNT, BIJ_DEF, LINV_DEF, BIJ_LINV_INV] >>
  `∀n. n < N ⇒ γ n < N ∧ δ n < N`
     by metis_tac[BIJ_DEF, INJ_THM, BIJ_LINV_BIJ, IN_COUNT] >>
  `(∀m n. m < N ∧ n < N ⇒ (δ m = δ n ⇔ m = n)) ∧
   (∀m n. m < N ∧ n < N ⇒ (γ m = γ n ⇔ m = n))` by metis_tac[] >>
  simp[loop_to_graph_FOLDR] >>
  `MAP (γ o δ) [0 ..< N] = [0 ..< N]`
    by simp[LIST_EQ_REWRITE, EL_MAP, EL_listRangeLHI] >>
  qabbrev_tac `add = add_action o mkEAction wf rds body` >>
  qabbrev_tac `mk' = mkEAction (wf o γ) (MAP (λf. f o γ) rds) (body o γ)` >>
  `FOLDR add emptyG [0 ..< N] = FOLDR add emptyG (MAP (γ o δ) [0 ..< N])`
    by simp[] >>
  `_ = FOLDR (add o γ) emptyG (MAP δ [0 ..< N])`
    by simp[GSYM MAP_MAP_o, FOLDR_MAP_o] >>
  `add o γ = add_action o (λa. a with iter updated_by γ) o mk'`
    by simp[Abbr`add`, Abbr`mk'`, Once FUN_EQ_THM, mkEAction_def,
            SINGL_APPLY_PERMUTE, SINGL_APPLY_MAP, MAP_MAP_o,
            combinTheory.o_ABS_R] >>
  pop_assum SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP δ [0 ..< N])` by simp[ALL_DISTINCT_MAP_INJ] >>
  `∀x. (mk' x).iter = x` by simp[Abbr`mk'`] >>
  `INJ (δ o γ) (iterations (FOLDR (add_action o mk') emptyG (MAP δ [0 ..< N])))
               UNIV`
    by dsimp[INJ_DEF, iterations_thm, IN_imap, imap_edges, MEM_MAP,
             Abbr`add`, IN_FOLD_add_action, Abbr`mk'`] >>
  `INJ γ (iterations (FOLDR (add_action o mk') emptyG (MAP δ [0 ..< N]))) UNIV`
    by (dsimp[INJ_THM, IN_FOLD_add_action, MEM_MAP, iterations_thm] >>
        simp[Abbr`mk'`, mkEAction_def]) >>
  pop_assum (assume_tac o MATCH_MP FOLDR_add_iterupd) >>
  pop_assum SUBST_ALL_TAC >> simp[imap_imap_o] >>
  qabbrev_tac `G' = FOLDR (add_action o mk') emptyG (MAP δ [0 ..< N])` >>
  `∀a. a ∈ G' ⇒ a.iter < N`
    by (dsimp[Abbr`G'`, IN_FOLD_add_action, GSYM FOLDR_MAP_o, MEM_MAP,
              MAP_MAP_o] >>
        dsimp[Abbr`mk'`, mkEAction_def]) >>
  `imap (δ o γ) G' = imap (λi. i) G'`
    by (ho_match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] imap_CONG) >>
        dsimp[iterations_thm]) >>
  simp[imap_ID] >> simp[Abbr`G'`] >>
  dsimp[graph_equality, IN_FOLD_add_action, MEM_MAP] >>
  conj_tac >- metis_tac[] >>
  `∀x y. mk' x = mk' y ⇔ x = y` by simp[Abbr`mk'`] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
    [FOLD_add_action_edges_ALL_DISTINCT, EL_listRangeLHI, EL_MAP] >>
  map_every qx_gen_tac [`a1`, `a2`] >> eq_tac >| [
    disch_then (qx_choosel_then [`i`, `j`] strip_assume_tac) >>
    map_every qexists_tac [`γ i`, `γ j`] >> simp[] >>
    qpat_assum `∀i0 i. i < N ∧ ddepR wf rsf i0 i ⇒ δ i0 < δ i`
      (qspecl_then [`γ j`, `γ i`] mp_tac) >>
    simp[ddepR_def] >>
    qmatch_abbrev_tac `¬(γ j < γ i) ∨ P ⇒ γ i < γ j` >>
    `¬P`
      by (qpat_assum `touches XX YY` mp_tac >>
          simp[touches_def, Abbr`mk'`, mkEAction_def, Abbr`P`, SINGL_APPLY_MAP,
               SINGL_APPLY_PERMUTE, MAP_MAP_o, combinTheory.o_ABS_R] >>
          strip_tac >> simp[]) >> simp[] >>
    `i < N` by decide_tac >>
    `γ i ≠ γ j` by simp[] >> decide_tac,

    disch_then (qx_choosel_then [`i`, `j`] strip_assume_tac) >>
    map_every qexists_tac [`δ i`, `δ j`]  >> simp[] >>
    first_x_assum match_mp_tac >> simp[ddepR_def] >>
    pop_assum mp_tac >>
    simp[touches_def, Abbr`mk'`, mkEAction_def, SINGL_APPLY_MAP,
         SINGL_APPLY_PERMUTE, MAP_MAP_o, combinTheory.o_ABS_R]
  ]);

val correctness = store_thm(
  "correctness",
  ``(∀i0 i. i < N ∧ ddepR wf rds i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N)
  ==>
    FOR (0,N) (eval wf rds body) =
    FOR (0,N) (eval (wf o γ)
                    (MAP (λf. f o γ) rds)
                    (body o γ))``,
  strip_tac >> pop_assum (assume_tac o SYM) >>
  `∀n. n < N ⇒ γ (δ n) = n ∧ δ (γ n) = n`
     by metis_tac[IN_COUNT, BIJ_DEF, LINV_DEF, BIJ_LINV_INV] >>
  `∀n. n < N ⇒ γ n < N ∧ δ n < N`
     by metis_tac[BIJ_DEF, INJ_THM, BIJ_LINV_BIJ, IN_COUNT] >>
  `(∀m n. m < N ∧ n < N ⇒ (δ m = δ n ⇔ m = n)) ∧
   (∀m n. m < N ∧ n < N ⇒ (γ m = γ n ⇔ m = n))` by metis_tac[] >>
  ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  qx_gen_tac `A` >>
  assume_tac
    (Q.INST [`lo` |-> `0`, `hi` |-> `N`, `rfs` |-> `rds`]
            loop_to_graph_correct) >>
  assume_tac
    (Q.INST [`lo` |-> `0`, `hi` |-> `N`,
             `rfs` |-> `MAP (λf. f o (γ:num->num)) rds`,
             `wf` |-> `wf o γ`, `body` |-> `body o γ`]
            loop_to_graph_correct) >>
  mp_tac (INST_TYPE [alpha |-> ``:num``, beta |-> alpha] same_graphs) >> simp[] >>
  disch_then SUBST_ALL_TAC >>
  qabbrev_tac `G = loop_to_graph (0,N) wf rds body` >>
  `INJ δ (iterations G) UNIV`
    by (dsimp[Abbr`G`, loop_to_graph_FOLDR, iterations_thm, INJ_DEF] >>
        qabbrev_tac `mk = mkEAction wf rds body` >>
        `∀x. (mk x).iter = x` by simp[Abbr`mk`] >>
        dsimp [IN_FOLD_add_action]) >>
  metis_tac[imap_irrelevance, graphs_evaluate_deterministically]);

val _ = export_theory();
