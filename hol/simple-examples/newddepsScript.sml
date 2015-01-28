open HolKernel Parse boolLib bossLib;
open primitivesTheory forLoopTheory pred_setTheory
open listRangeTheory
open listTheory
open lcsymtacs

open actionTheory
open dagTheory

fun fds thl = full_simp_tac (srw_ss() ++ boolSimps.DNF_ss) thl

val _ = new_theory "newddeps";

val eval_def = Define`
  eval Wf Rs vf i A =
    update A (Wf i) (vf i (MAP (λf. vsub A (f i)) Rs))
`;

val apply_action_def = Define`
  apply_action (a:(num # (α list -> α),num)node) (A:'a mvector) =
    case a.write of
        NONE => A
      | SOME w => update A w (SND a.data (MAP (vsub A) a.reads))
`;

val MAP_vsub = store_thm(
  "MAP_vsub",
  ``¬MEM w reads ⇒ MAP ($' (update A w e)) reads = MAP ($' A) reads``,
  Induct_on `reads` >> simp[update_sub]);

val nontouching_actions_commute = store_thm(
  "nontouching_actions_commute",
  ``¬touches a1 a2 ⇒
    apply_action a1 (apply_action a2 A) = apply_action a2 (apply_action a1 A)``,
  simp[touches_def, apply_action_def, vector_EQ] >> rpt strip_tac >>
  map_every Cases_on [`a1.write`, `a2.write`] >> fs[] >>
  ONCE_REWRITE_TAC [update_sub] >> simp[] >>
  qmatch_assum_rename_tac `a1.write = SOME w1` [] >>
  Cases_on `i = w1` >> simp[]
  >- (simp[SimpRHS, update_sub] >>
      Cases_on `w1 < vsz A` >>
      simp[update_sub, MAP_vsub]) >>
  simp[update_sub, MAP_vsub]);

val actions_commute' = prove(
  ``a2 ≁ₜ a1 ⇒
    apply_action a1 (apply_action a2 A) = apply_action a2 (apply_action a1 A)``,
  metis_tac[touches_SYM, nontouching_actions_commute]);

val evalG_def = new_specification("evalG_def",
  ["evalG"],
  dag_recursion
    |> ISPEC ``λa r m : α mvector. r (apply_action a m) : α mvector``
    |> SPEC ``λm:α mvector. m``
    |> SIMP_RULE (srw_ss()) [FUN_EQ_THM, actions_commute']);
val _ = export_rewrites ["evalG_def"]

val mkEAction_def = Define`
  mkEAction wf rfs body i =
    <| write := SOME (wf i); reads := rfs <*> [i];
       data := (i,body i); ident := () |>
`;

val mkEAction_11 = store_thm(
  "mkEAction_11",
  ``mkEAction wf rfs body i = mkEAction wf rfs body j ⇔ i = j``,
  simp[mkEAction_def, EQ_IMP_THM]);
val _ = export_rewrites ["mkEAction_11"]

val loop_to_graph_def = tDefine "loop_to_graph" `
  loop_to_graph (lo,hi) wf rfs body =
    if lo < hi then
      mkEAction wf rfs body lo <+
                 (loop_to_graph (lo+1,hi) wf rfs body)
    else ε
` (WF_REL_TAC `measure (λp. SND (FST p) - FST (FST p))`)

val loop_to_graph_FOLDR = store_thm(
  "loop_to_graph_FOLDR",
  ``loop_to_graph (lo,hi) wf rfs body =
      FOLDR (dagAdd o mkEAction wf rfs body)
            ε
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

val loop_to_graph_idents = store_thm(
  "loop_to_graph_idents",
  ``loop_to_graph (lo,hi) wf rfs body = G ⇒
      (∀a. a ∈ G ⇒ lo ≤ FST a.data ∧ FST a.data < hi)``,
  qid_spec_tac `G` >> Induct_on `hi - lo` >>
  ONCE_REWRITE_TAC [loop_to_graph_def] >- simp[] >>
  rpt gen_tac >> qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> qx_gen_tac `G` >> simp[] >>
  `∃G0. loop_to_graph (lo + 1, hi) wf rfs body = G0` by simp[] >>
  `n = hi - (lo + 1)` by decide_tac >>
  `(∀a. a ∈ G0 ⇒ lo + 1 ≤ FST a.data ∧ FST a.data < hi)` by metis_tac[] >>
  simp[] >> disch_then (SUBST_ALL_TAC o SYM) >> simp[] >> rpt strip_tac
  >- rw[mkEAction_def]
  >- simp[mkEAction_def]
  >- (res_tac >> simp[])
  >- (res_tac >> simp[]));

val mkEAction_ident = store_thm(
  "mkEAction_ident",
  ``FST (mkEAction wf rfs body i).data = i``,
  simp[mkEAction_def]);
val _ = export_rewrites ["mkEAction_ident"]

val loop_to_graph_correct = store_thm(
  "loop_to_graph_correct",
  ``evalG (loop_to_graph (lo,hi) wf rfs body) A =
    FOR (lo,hi) (eval wf rfs body) A``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- simp[Once FOR_def, Once loop_to_graph_def] >>
  rpt gen_tac >>
  qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> qx_gen_tac `A` >>
  simp[Once FOR_def] >> simp[Once loop_to_graph_def] >>
  simp[eval_apply_action]);

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
    polydata_upd (f ## I) o
    mkEAction (wf o f) (MAP (\rf. rf o f) rfs) (body o f)``,
  simp[FUN_EQ_THM, mkEAction_def, SINGL_APPLY_PERMUTE, MAP_MAP_o,
       combinTheory.o_ABS_R, SINGL_APPLY_MAP, polydata_upd_def]);

val ALL_DISTINCT_MAP_INJ = store_thm(
  "ALL_DISTINCT_MAP_INJ",
  ``(!x y. MEM x l ∧ MEM y l ==> ((f x = f y) <=> (x = y))) ⇒
    (ALL_DISTINCT (MAP f l) <=> ALL_DISTINCT l)``,
  Induct_on `l` THEN ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP] THEN
  METIS_TAC[]);

val apply_action_d1 = store_thm(
  "apply_action_d1[simp]",
  ``apply_action (polydata_upd (f ## I) a) m = apply_action a m``,
  simp[polydata_upd_def, apply_action_def]);

val evalG_dagmap1 = store_thm(
  "evalG_dagmap1[simp]",
  ``∀g m. evalG (dagmap (f ## I) g) m = evalG g m``,
  ho_match_mp_tac dag_ind >> simp[])

val pairmap_compose = store_thm(
  "pairmap_compose",
  ``(f1 ## f2) o (g1 ## g2) = (f1 o g1) ## (f2 o g2)``,
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]);

val same_graphs = store_thm(
  "same_graphs",
  ``(∀i0 i. i < N ∧ ddepR wf rds i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N) ⇒
    loop_to_graph (0,N) (wf o γ) (MAP (λf. f o γ) rds) (body o γ) =
      dagmap (δ ## I) (loop_to_graph (0,N) wf rds body)``,
  strip_tac >> pop_assum (assume_tac o SYM) >>
  `∀n. n < N ⇒ γ (δ n) = n ∧ δ (γ n) = n`
     by metis_tac[IN_COUNT, BIJ_DEF, LINV_DEF, BIJ_LINV_INV] >>
  `∀n. n < N ⇒ γ n < N ∧ δ n < N`
     by metis_tac[BIJ_DEF, INJ_IFF, BIJ_LINV_BIJ, IN_COUNT] >>
  `(∀m n. m < N ∧ n < N ⇒ (δ m = δ n ⇔ m = n)) ∧
   (∀m n. m < N ∧ n < N ⇒ (γ m = γ n ⇔ m = n))` by metis_tac[] >>
  simp[loop_to_graph_FOLDR] >>
  `MAP (γ o δ) [0 ..< N] = [0 ..< N]`
    by simp[LIST_EQ_REWRITE, EL_MAP, EL_listRangeLHI] >>
  qabbrev_tac `add = dagAdd o mkEAction wf rds body` >>
  qabbrev_tac `mk' = mkEAction (wf o γ) (MAP (λf. f o γ) rds) (body o γ)` >>
  `FOLDR add ε [0 ..< N] = FOLDR add ε (MAP (γ o δ) [0 ..< N])`
    by simp[] >>
  `_ = FOLDR (add o γ) ε (MAP δ [0 ..< N])`
    by simp[GSYM MAP_MAP_o, FOLDR_MAP_o] >>
  `add o γ = dagAdd o polydata_upd (γ ## I) o mk'`
    by simp[Abbr`add`, Abbr`mk'`, Once FUN_EQ_THM, mkEAction_def,
            SINGL_APPLY_PERMUTE, SINGL_APPLY_MAP, MAP_MAP_o,
            combinTheory.o_ABS_R, polydata_upd_def] >>
  pop_assum SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP δ [0 ..< N])` by simp[ALL_DISTINCT_MAP_INJ] >>
  fs[FOLDR_dagAdd_dataupd] >> simp[dagmap_dagmap_o, pairmap_compose] >>
  qabbrev_tac `G' = FOLDR (dagAdd o mk') ε (MAP δ [0 ..< N])` >>
  `dagmap (δ o γ ## I) G' = dagmap I G'`
    by (ho_match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] dagmap_CONG) >>
        simp[pairTheory.FORALL_PROD, PULL_EXISTS] >> rpt strip_tac >>
        qmatch_rename_tac `δ (γ i) = i` [] >> `i < N` suffices_by simp[] >>
        pop_assum mp_tac >>
        simp[Abbr`G'`, MEM_MAP, PULL_EXISTS, Abbr`mk'`, mkEAction_def] >>
        rw[] >> fs[]) >>
  simp[Abbr`G'`] >>
  simp[GSYM FOLDR_MAP_o] >>
  match_mp_tac BIJ_FOLDR_add_EQ >> simp[] >>
  qexists_tac `γ` >> csimp[EL_MAP, EL_listRangeLHI] >> conj_tac
  >- (Q.UNDISCH_THEN `LINV δ (count N) = γ` (SUBST_ALL_TAC o SYM) >>
      simp[BIJ_LINV_BIJ]) >>
  simp[Abbr`mk'`, mkEAction_def] >>
  map_every qx_gen_tac [`i`, `j`] >>
  first_x_assum (qspecl_then [`γ j`, `γ i`] mp_tac o
                 assert (can (find_term (same_const ``ddepR``)) o
                         concl)) >>
  csimp[AND_IMP_INTRO, ddepR_def, touches_def] >>
  map_every (fn q => Cases_on q >> simp[])
     [`γ i < γ j`, `i < j`, `j < N`] >>
  `γ i ≠ γ j` by simp[] >>
  Cases_on `wf (γ j) = wf (γ i)` >> simp[] >>
  simp[SINGL_APPLY_MAP, SINGL_APPLY_PERMUTE, MAP_MAP_o,
       combinTheory.o_ABS_R, MEM_MAP] >>
  metis_tac[])

val correctness = store_thm(
  "correctness",
  ``(∀i0 i. i < N ∧ ddepR wf rds i0 i ⇒ δ i0 < δ i) ∧
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
     by metis_tac[BIJ_DEF, INJ_IFF, BIJ_LINV_BIJ, IN_COUNT] >>
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
  mp_tac (INST_TYPE [alpha |-> ``:num``, beta |-> ``:α list -> α``]
                    same_graphs) >>
  simp[] >>
  disch_then SUBST_ALL_TAC >>
  qabbrev_tac `G = loop_to_graph (0,N) wf rds body` >>
  metis_tac[evalG_dagmap1]);

val _ = export_theory();
