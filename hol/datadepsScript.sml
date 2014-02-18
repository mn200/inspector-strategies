open HolKernel Parse boolLib bossLib;
open primitivesTheory forLoopTheory pred_setTheory
open listRangeTheory
open listTheory
open lcsymtacs

fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun dsimp thl = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) thl
fun csimp thl = asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss) thl

val _ = new_theory "datadeps";

val _ = set_mapped_fixity { fixity = Infixl 500, term_name = "FAPPLY",
                            tok = "<*>" }
val _ = overload_on ("FAPPLY", ``LIST_APPLY``)


val eval_def = Define`
  eval Wf Rs vf i A =
    update A (Wf i) (vf i (MAP (λf. vsub A (f i)) Rs))
`;

val _ = Hol_datatype`
  action = <|
    write : num ;
    reads : num list ;
    expr : 'a list -> 'a;
    iter : num
  |>
`;

val apply_action_def = Define`
  apply_action (a:'a action) (A:'a mvector) =
    update A a.write (a.expr (MAP (vsub A) a.reads))
`;

val touches_def = Define`
  touches a1 a2 ⇔
     a1.write = a2.write ∨ MEM a1.write a2.reads ∨ MEM a2.write a1.reads
`;

val touches_ignores_iter = store_thm(
  "touches_ignores_iter",
  ``(touches a1 (a2 with iter updated_by f) ⇔ touches a1 a2) ∧
    (touches (a1 with iter updated_by f) a2 ⇔ touches a1 a2)``,
  simp[touches_def]);
val _ = export_rewrites ["touches_ignores_iter"]


val MAP_vsub = store_thm(
  "MAP_vsub",
  ``¬MEM w reads ⇒ MAP ($' (update A w e)) reads = MAP ($' A) reads``,
  Induct_on `reads` >> simp[update_sub]);

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



val touches_REFL = store_thm(
  "touches_REFL",
  ``touches a a``,
  simp[touches_def]);
val _ = export_rewrites ["touches_REFL"]

val touches_SYM = store_thm(
  "touches_SYM",
  ``touches a1 a2 ⇒ touches a2 a1``,
  simp[touches_def] >> rpt strip_tac >> simp[]);

val _ = Hol_datatype`action_graph = <| nodes : 'a action set;
                                       edges : 'a action -> 'a action set |>`

val _ = overload_on ("IN", ``λa:'a action G:'a action_graph. a ∈ G.nodes``)

val graph_equality = store_thm(
  "graph_equality",
  ``G1 = G2 ⇔
      (∀a. a ∈ G1 ⇔ a ∈ G2) ∧ (∀a1 a2. G1.edges a1 a2 ⇔ G2.edges a1 a2)``,
  simp[theorem "action_graph_component_equality", Once EQ_IMP_THM] >>
  strip_tac >> conj_tac >- simp[EXTENSION] >> simp[FUN_EQ_THM]);

val wfG_def = Define`
  wfG G ⇔
      FINITE G.nodes ∧
      (∀a1 a2. G.edges a1 a2 ⇒ touches a1 a2 ∧ a1 ∈ G ∧ a2 ∈ G) ∧
      (∀a1 a2. a1 ∈ G ∧ a2 ∈ G ∧ touches a1 a2 ∧ a1 ≠ a2 ⇒ (¬G.edges a1 a2 ⇔ G.edges a2 a1)) ∧
      ∀a1 a2. a1 ∈ G ∧ a2 ∈ G ∧ G.edges⁺ a1 a2 ⇒ ¬G.edges⁺ a2 a1
`;

val emptyG_def = Define`
  emptyG = <| nodes := ∅; edges := REMPTY |>
`;

val IN_emptyG = store_thm(
  "IN_emptyG",
  ``a ∈ emptyG ⇔ F``,
  simp[emptyG_def]);
val _ = export_rewrites ["IN_emptyG"]

val emptyG_edges = store_thm(
  "emptyG_edges",
  ``emptyG.edges x y ⇔ F``,
  simp[emptyG_def]);
val _ = export_rewrites ["emptyG_edges"]

val emptyG_nodes = store_thm(
  "emptyG_nodes",
  ``emptyG.nodes = ∅``,
  simp[emptyG_def]);
val _ = export_rewrites ["emptyG_nodes"]

val wfG_empty = store_thm(
  "wfG_empty",
  ``wfG emptyG``,
  simp[wfG_def, emptyG_def]);
val _ = export_rewrites ["wfG_empty"]

val wfG_irrefl = store_thm(
  "wfG_irrefl",
  ``wfG G ∧ x ∈ G ⇒ ¬G.edges x x``,
  simp[wfG_def] >> rpt strip_tac >>
  metis_tac[relationTheory.TC_SUBSET]);

val gDELETE_def = Define`
  gDELETE G a = <| nodes := G.nodes DELETE a; edges := G.edges \\ a |>
`;
val _ = overload_on ("\\\\", ``gDELETE``)

val IN_gDELETE = store_thm(
  "IN_gDELETE",
  ``a ∈ G \\ b ⇔ a ∈ G ∧ a ≠ b``,
  simp[gDELETE_def]);
val _ = export_rewrites ["IN_gDELETE"]

val gDELETE_edges = store_thm(
  "gDELETE_edges",
  ``(G \\ a).edges b c ⇔ G.edges b c ∧ a ≠ b``,
  simp[gDELETE_def] >> metis_tac[]);
val _ = export_rewrites ["gDELETE_edges"]

val gDELETE_commutes = store_thm(
  "gDELETE_commutes",
  ``(G:'a action_graph) \\ a1 \\ a2 = G \\ a2 \\ a1``,
  simp[gDELETE_def, theorem "action_graph_component_equality", DELETE_COMM] >>
  simp[FUN_EQ_THM] >> metis_tac[]);

val wfGs_pull_apart = store_thm(
  "wfGs_pull_apart",
  ``wfG G ∧ a ∈ G ∧ (∀a'. a' ∈ G ⇒ ¬G.edges a' a) ⇒ wfG (G \\ a)``,
  simp[wfG_def, gDELETE_def] >> rw[] >>
  metis_tac[relationTheory.TC_MONOTONE, relationTheory.RDOM_DELETE_DEF]);

val _ = IndDefLib.export_rule_induction "relation.TC_STRONG_INDUCT"
val TC_in_R = store_thm(
  "TC_in_R",
  ``∀x y. R⁺ x y ⇒ (∃z. R x z) ∧ (∃z. R z y)``,
  Induct_on `R⁺ x y` >> metis_tac[]);

val wfG_WF = store_thm(
  "wfG_WF",
  ``wfG G ⇒ WF G.edges``,
  simp[wfG_def] >> strip_tac >>
  `G.edges = REL_RESTRICT G.edges G.nodes`
    by (simp[REL_RESTRICT_DEF, FUN_EQ_THM, EQ_IMP_THM] >>
        metis_tac[]) >>
  first_assum (fn th => simp[FINITE_WF_noloops, Once th]) >>
  pop_assum (SUBST_ALL_TAC o SYM) >>
  simp[relationTheory.irreflexive_def] >> metis_tac[TC_in_R]);

val wfG_FINITE = store_thm(
  "wfG_FINITE",
  ``wfG G ⇒ FINITE G.nodes``,
  simp[wfG_def]);

val nonempty_wfG_has_points = store_thm(
  "nonempty_wfG_has_points",
  ``wfG G ∧ G.nodes ≠ ∅ ⇒
    ∃e. e ∈ G ∧ ∀e'. e' ∈ G ⇒ ¬G.edges e' e``,
  rpt strip_tac >>
  `WF G.edges` suffices_by
    (simp[relationTheory.WF_DEF, IN_DEF] >>
     pop_assum mp_tac >> simp[GSYM MEMBER_NOT_EMPTY, IN_DEF] >>
     metis_tac[]) >>
  metis_tac[wfG_WF]);

val (evalG_rules,evalG_ind,evalG_cases) = Hol_reln`
  (∀A. evalG A emptyG A) ∧
  (∀a A0 G A.
      a ∈ G ∧ (∀a'. a' ∈ G ⇒ ¬G.edges a' a) ∧
      evalG (apply_action a A0) (G \\ a) A ⇒
      evalG A0 G A)
`;

val evalG_EMPTY = store_thm(
  "evalG_EMPTY",
  ``evalG A0 emptyG A ⇔ A = A0``,
  simp[Once evalG_cases]);
val _ = export_rewrites ["evalG_EMPTY"]

val INSERT_11 = store_thm(
  "INSERT_11",
  ``e ∉ s1 ∧ e ∉ s2 ⇒ (e INSERT s1 = e INSERT s2 ⇔ s1 = s2)``,
  simp[EQ_IMP_THM] >> simp[EXTENSION] >> metis_tac[]);

val _ = overload_on ("gCARD", ``\g. CARD g.nodes``)

val gCARD_EQ_0 = store_thm(
  "gCARD_EQ_0",
  ``wfG G ⇒ (gCARD G = 0 ⇔ G = emptyG)``,
  simp[emptyG_def, wfG_def, EQ_IMP_THM] >> rpt strip_tac >> fs[] >>
  simp[theorem "action_graph_component_equality", FUN_EQ_THM]);

val gCARD_gDELETE = store_thm(
  "gCARD_gDELETE",
  ``wfG G ∧ a ∈ G ⇒ gCARD (G \\ a) = gCARD G - 1``,
  simp[wfG_def, gDELETE_def]);
val _ = export_rewrites ["gCARD_gDELETE"]

val evalG_total = store_thm(
  "evalG_total",
  ``wfG G ⇒ ∃A'. evalG A G A'``,
  qid_spec_tac `A` >> Induct_on `gCARD G`
  >- (simp[Once evalG_cases] >> metis_tac[gCARD_EQ_0]) >>
  rpt strip_tac >>
  `G.nodes ≠ ∅` by (strip_tac >> fs[]) >>
  `∃a. a ∈ G ∧ ∀a'. a' ∈ G ⇒ ¬G.edges a' a`
    by metis_tac[nonempty_wfG_has_points] >>
  `wfG (G \\ a)` by metis_tac[wfGs_pull_apart] >>
  `gCARD (G \\ a) = v` by simp[] >>
  metis_tac[evalG_rules]);

val wfG_evaluate_deterministically = store_thm(
  "wfG_evaluate_deterministically",
  ``wfG G ∧ evalG A0 G A ⇒ ∀A'. evalG A0 G A' ⇒ A' = A``,
  map_every qid_spec_tac [`A0`, `A`] >>
  completeInduct_on `gCARD G` >> qx_gen_tac `G` >>
  qmatch_rename_tac `n = gCARD G ⇒ XX` ["XX"] >> strip_tac >>
  map_every qx_gen_tac [`A`, `A0`] >> strip_tac >>
  qx_gen_tac `A'` >> strip_tac >>
  full_simp_tac (srw_ss() ++ boolSimps.DNF_ss)
    [AND_IMP_INTRO, GSYM CONJ_ASSOC] >> rw[] >>
  qpat_assum `evalG A0 G A` mp_tac >>
  simp[Once evalG_cases] >>
  disch_then (DISJ_CASES_THEN2
                strip_assume_tac
                (qx_choose_then `a1` strip_assume_tac))
  >- fs[] >>
  `G ≠ emptyG` by (strip_tac >> fs[]) >>
  qpat_assum `evalG XX YY A'` mp_tac >>
  simp[Once evalG_cases] >>
  disch_then (qx_choose_then `a2` strip_assume_tac) >>
  `wfG (G \\ a1) ∧ wfG (G \\ a2)` by simp[wfGs_pull_apart] >>
  Cases_on `a2 = a1`
  >- (rw[] >> first_x_assum (qspecl_then [`G \\ a1`, `A'`] match_mp_tac) >>
      qexists_tac `apply_action a1 A0` >> simp[] >>
      metis_tac[IN_emptyG, gCARD_EQ_0, DECIDE ``¬(0 < x) ⇔ x = 0``]) >>
  `apply_action a1 (apply_action a2 A0) = apply_action a2 (apply_action a1 A0)`
    by (match_mp_tac nontouching_actions_commute >> metis_tac [wfG_def]) >>
  `wfG (G \\ a1 \\ a2)` by simp[wfGs_pull_apart] >>
  `∃A2. evalG (apply_action a1 (apply_action a2 A0)) (G \\ a1 \\ a2) A2`
    by metis_tac[evalG_total] >>
  `evalG (apply_action a1 A0) (G \\ a1) A2 ∧
   evalG (apply_action a2 A0) (G \\ a2) A2`
    by (conj_tac >> match_mp_tac (CONJUNCT2 evalG_rules) >| [
          qexists_tac `a2`, qexists_tac `a1`] >> simp[] >>
        metis_tac[gDELETE_commutes]) >>
  `gCARD (G \\ a1) < gCARD G ∧ gCARD (G \\ a2) < gCARD G` suffices_by
     metis_tac[] >>
  simp[] >>
  metis_tac [gCARD_EQ_0, IN_emptyG, DECIDE ``¬(0 < x) ⇔ x = 0``])

val add_action_def = Define`
  add_action a G =
    if a ∈ G then G
    else
      <| nodes := a INSERT G.nodes ;
         edges := (λsrc tgt. G.edges src tgt ∨
                             src = a ∧ touches a tgt ∧ tgt ∈ G.nodes) |>
`;

val IN_add_action = store_thm(
  "IN_add_action",
  ``a1 ∈ add_action a2 G ⇔ a1 = a2 ∨ a1 ∈ G``,
  simp[add_action_def] >> rw[EQ_IMP_THM] >> simp[]);
val _ = export_rewrites ["IN_add_action"]

val add_action_edges = store_thm(
  "add_action_edges",
  ``(add_action a G).edges a1 a2 ⇔
    ¬(a ∈ G) ∧ a1 = a ∧ a2 ∈ G ∧ touches a1 a2 ∨ G.edges a1 a2``,
  rw[add_action_def] >> metis_tac[]);
val _ = export_rewrites ["add_action_edges"]



val add_action_lemma = prove(
  ``(∀a1 a2. R' a1 a2 ⇒ R a1 a2 ∨ a1 = a ∧ a2 ≠ a) ∧ (∀b. ¬R a b ∧ ¬R b a) ⇒
     ∀a1 a2. R'⁺ a1 a2 ⇒ a2 ≠ a ∧ a1 = a ∨ R⁺ a1 a2``,
  strip_tac >> Induct_on `R'⁺` >> conj_tac >- metis_tac[relationTheory.TC_SUBSET] >>
  rpt strip_tac >> simp[]
  >- metis_tac[TC_in_R]
  >- metis_tac[TC_in_R] >>
  metis_tac[relationTheory.TC_RULES]);

val wfG_add_action = store_thm(
  "wfG_add_action",
  ``wfG G ⇒ wfG (add_action a G)``,
  simp[add_action_def] >>
  qabbrev_tac
    `R' = (λsrc tgt. G.edges src tgt ∨ src = a ∧ touches a tgt ∧ tgt ∈ G)`>>
  Cases_on `a ∈ G` >> simp[] >>
  `∀a1 a2. G.edges a1 a2 ∨ a1 = a ∧ touches a a2 ∧ a2 ∈ G ⇔ R' a1 a2` by simp[Abbr`R'`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  simp[wfG_def] >> reverse (rpt strip_tac)
  >- (`∀b. ¬G.edges a b ∧ ¬G.edges b a` by metis_tac[] >>
      `∀a1 a2. R' a1 a2 ⇒ G.edges a1 a2 ∨ a1 = a ∧ a2 ≠ a` by metis_tac[] >>
      pop_assum
        (fn c1 => pop_assum
           (fn c2 => assume_tac (MATCH_MP add_action_lemma (CONJ c1 c2)))) >>
      metis_tac[]) >>
  metis_tac[TC_in_R, touches_SYM]);

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
  asimp[Once loop_to_graph_def,listRangeLHI_EMPTY, listRangeLHI_CONS]);

val wfG_FOLDR_add_action = store_thm(
  "wfG_FOLDR_add_action",
  ``wfG (FOLDR (add_action o f) emptyG l)``,
  Induct_on `l` >> simp[wfG_add_action]);

val wfG_loop_to_graph = store_thm(
  "wfG_loop_to_graph",
  ``wfG (loop_to_graph (lo, hi) wf rfs body)``,
  simp[loop_to_graph_FOLDR, wfG_FOLDR_add_action]);

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
      (∀a1 a2. G.edges a1 a2 ⇒ a1 ∈ G ∧ a2 ∈ G)``,
  qid_spec_tac `G` >> Induct_on `hi - lo` >>
  ONCE_REWRITE_TAC [loop_to_graph_def] >- simp[] >>
  rpt gen_tac >> qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> qx_gen_tac `G` >> simp[] >>
  `∃G0. loop_to_graph (lo + 1, hi) wf rfs body = G0` by simp[] >>
  `n = hi - (lo + 1)` by decide_tac >>
  `(∀a. a ∈ G0 ⇒ lo + 1 ≤ a.iter ∧ a.iter < hi) ∧
   ∀a1 a2. G0.edges a1 a2 ⇒ a1 ∈ G0 ∧ a2 ∈ G0` by metis_tac[] >>
  simp[add_action_def] >> rw[] >> fs[mkEAction_def]
  >- (res_tac >> decide_tac)
  >- res_tac
  >- res_tac
  >- (res_tac >> decide_tac)
  >- decide_tac
  >- metis_tac[]
  >- metis_tac[]);

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
  simp[add_action_def] >>
  `¬(mkEAction wf rfs body lo ∈ G)`
    by (strip_tac >>
        `lo + 1 ≤ (mkEAction wf rfs body lo).iter`
          by metis_tac[loop_to_graph_iterations] >>
        full_simp_tac (srw_ss() ++ ARITH_ss) [mkEAction_def]) >>
  qexists_tac `mkEAction wf rfs body lo` >>
  simp[] >> csimp[] >>
  `(∀a. a ∈ G ⇒ lo + 1 ≤ a.iter ∧ a.iter < hi) ∧
   ∀a1 a2. G.edges a1 a2 ⇒ a1 ∈ G ∧ a2 ∈ G`
    by metis_tac[loop_to_graph_iterations] >>
  `(mkEAction wf rfs body lo).iter = lo ∧ ¬(lo + 1 ≤ lo)`
    by simp[mkEAction_def] >>
  conj_tac >- metis_tac[] >>
  qmatch_abbrev_tac `
    evalG AA GG (FOR (lo + 1, hi) (eval wf rfs body) AA)
  ` >>
  `n = hi - (lo + 1)` by decide_tac >>
  `GG = G` suffices_by metis_tac[] >>
  qunabbrev_tac `GG` >>
  simp[theorem "action_graph_component_equality"] >>
  conj_tac >- (csimp[EXTENSION] >> metis_tac[]) >>
  csimp[FUN_EQ_THM] >> metis_tac[]);

val RIMAGE_DEF = new_definition(
  "RIMAGE_DEF",
  ``RIMAGE f R x y <=> ?a b. (x = f a) /\ (y = f b) /\ R a b``);

val RIMAGE_REMPTY = store_thm(
  "RIMAGE_REMPTY",
  ``RIMAGE f REMPTY = REMPTY``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, RIMAGE_DEF]);
val _ = export_rewrites ["RIMAGE_REMPTY"]

val imap_def = Define`
  imap (f:'a action -> num) (G: 'a action_graph) =
     G with <| nodes updated_by IMAGE (λa. a with iter := f a);
               edges updated_by RIMAGE (λa. a with iter := f a) |>
`;

val imap_emptyG = store_thm(
  "imap_emptyG",
  ``imap f emptyG = emptyG``,
  simp[emptyG_def, imap_def]);
val _ = export_rewrites ["imap_emptyG"]

val IN_imap = store_thm(
  "IN_imap",
  ``a ∈ imap f G ⇔ ∃a0. a0 ∈ G ∧ a = a0 with iter := f a0``,
  simp[imap_def] >> metis_tac[]);
val _ = export_rewrites ["IN_imap"]

val imap_edges = store_thm(
  "imap_edges",
  ``(imap f G).edges a1 a2 ⇔
      ∃a10 a20. G.edges a10 a20 ∧ a1 = a10 with iter := f a10 ∧
                a2 = a20 with iter := f a20``,
  simp[imap_def, RIMAGE_DEF] >> metis_tac[]);

val INJ_THM = store_thm(
  "INJ_THM",
  ``INJ f s t ⇔
      (∀x. x ∈ s ⇒ f x ∈ t) ∧
      ∀x y. x ∈ s ∧ y ∈ s ⇒ (f x = f y ⇔ x = y)``,
  metis_tac[INJ_DEF]);

val imap_add_action = store_thm(
  "imap_add_action",
  ``INJ f (a INSERT G.nodes) Is ⇒
    (imap f (add_action a G) = add_action (a with iter := f a) (imap f G))``,
  simp[graph_equality, imap_edges, IN_imap] >> rpt strip_tac
  >- metis_tac[] >>
  `∀a1 a2. (a1 = a ∨ a1 ∈ G) ∧ (a2 = a ∨ a2 ∈ G) ⇒
           (a1 with iter := f a1 = a2 with iter := f a2 ⇔
            a1 = a2)`
    by (simp[EQ_IMP_THM] >> fs[INJ_THM] >>
        rpt gen_tac >> strip_tac >> simp[theorem "action_component_equality"]) >>
  eq_tac >> rpt strip_tac >> csimp[]
  >- (disj1_tac >> rw[] >> qmatch_rename_tac `b ∉ G.nodes ∨ XX` ["XX"] >>
      Cases_on `b ∈ G` >> simp[] >> strip_tac >> fs[])
  >- metis_tac[]
  >- (`a ∉ G.nodes` by metis_tac[] >> dsimp[] >> csimp[] >> rw[] >> fs[]) >>
  metis_tac[]);

val apply_action_ignores_iter = store_thm(
  "apply_action_ignores_iter",
  ``apply_action (a with iter updated_by f) A = apply_action a A``,
  simp[apply_action_def]);
val _ = export_rewrites ["apply_action_ignores_iter"]

val imap_irrelevance = store_thm(
  "imap_irrelevance",
  ``∀A0 G A.
      evalG A0 G A ⇒
      wfG G ⇒
        ∀f Is. INJ f G.nodes Is ⇒ evalG A0 (imap f G) A``,
  Induct_on `evalG` >> rpt strip_tac >> simp[] >>
  match_mp_tac (CONJUNCT2 evalG_rules) >> dsimp[imap_edges] >>
  qexists_tac `a` >> simp[] >> `wfG (G \\ a)` by simp[wfGs_pull_apart] >> fs[]>>
  `∀a1 a2. a1 ∈ G ∧ a2 ∈ G ⇒
           (a1 with iter := f a1 = a2 with iter := f a2 ⇔
            a1 = a2)`
    by (rpt strip_tac >> fs[INJ_THM] >> simp[EQ_IMP_THM] >>
        simp[theorem "action_component_equality"]) >>
  reverse conj_tac
  >- (`imap f G \\ (a with iter := f a) = imap f (G \\ a)` suffices_by
          (rw[] >> first_x_assum match_mp_tac >> fs[INJ_THM] >> metis_tac[]) >>
      dsimp[graph_equality, imap_edges, EQ_IMP_THM] >> csimp[] >>
      rpt strip_tac
      >- (pop_assum mp_tac >> `a10 ∈ G` by metis_tac[wfG_def] >> simp[] >>
          metis_tac[]) >>
      `a10 ∈ G` by metis_tac [wfG_def] >> metis_tac[]) >>
  rpt gen_tac >>
  qmatch_rename_tac `a0 ∈ G ⇒ ¬G.edges a1' a2' ∨ XX` ["XX"] >> strip_tac >>
  Cases_on `G.edges a1' a2'` >> simp[] >>
  `a1' ∈ G ∧ a2' ∈ G` by metis_tac[wfG_def] >> simp[] >> metis_tac[]);

val imap_imap_o = store_thm(
  "imap_imap_o",
  ``imap f (imap g G) = imap (λa. f (a with iter := g a)) G``,
  simp[graph_equality, IN_imap, imap_edges] >> rpt strip_tac >>
  dsimp[]);

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
  simp[FUN_EQ_THM, mkEAction_def,
       REWRITE_RULE [SINGL_DEF] SINGL_APPLY_PERMUTE,
       REWRITE_RULE [SINGL_DEF] SINGL_APPLY_MAP, MAP_MAP_o,
       combinTheory.o_ABS_R]);

val IN_FOLD_add_action = store_thm(
  "IN_FOLD_add_action",
  ``a ∈ FOLDR (add_action o f) emptyG l ⇔ ∃i. MEM i l ∧ a = f i``,
  Induct_on `l` >> simp[] >> rw[EQ_IMP_THM] >> metis_tac[]);

(* the ALL_DISTINCT assumption is reasonable given our setting *)
val FOLD_add_action_edges_ALL_DISTINCT = store_thm(
  "FOLD_add_action_edges_ALL_DISTINCT",
  ``ALL_DISTINCT l ∧ (∀x y. f x = f y ⇔ x = y) ⇒
    ((FOLDR (add_action o f) emptyG l).edges a1 a2 ⇔
     ∃i j. i < j ∧ j < LENGTH l ∧ a1 = f (EL i l) ∧ a2 = f (EL j l) ∧
           touches a1 a2)``,
  Induct_on `l` >> simp[IN_FOLD_add_action] >> qx_gen_tac `h` >> strip_tac >>
  fs[] >> qpat_assum `XX a1 a2 ⇔ YY` kall_tac >> eq_tac >> strip_tac >| [
    qmatch_assum_rename_tac `MEM i l` [] >>
    `∃n. n < LENGTH l ∧ i = EL n l` by metis_tac[MEM_EL] >>
    map_every qexists_tac [`0`, `SUC n`] >> simp[],
    qmatch_assum_rename_tac `a1 = f (EL i l)` [] >>
    qmatch_assum_rename_tac `a2 = f (EL j l)` [] >>
    map_every qexists_tac [`SUC i`, `SUC j`] >> simp[],
    qmatch_assum_rename_tac `a1 = f (EL i (h::l))` [] >>
    qmatch_assum_rename_tac `a2 = f (EL j (h::l))` [] >>
    `i = 0 ∨ ∃i0. i = SUC i0` by (Cases_on `i` >> simp[])
    >- (disj1_tac >> fs[] >>
        `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >>
        fs[] >> metis_tac[MEM_EL]) >>
    disj2_tac >>
    `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
    metis_tac[]
  ]);

val FOLD_add_action_edges = store_thm(
  "FOLD_add_action_edges",
  ``(FOLDR (add_action o mkEAction wf rfs body) emptyG l).edges a1 a2 ⇔
     ∃i j. i < j ∧ j < LENGTH l ∧ (∀k. j <= k ∧ k < LENGTH l ⇒ EL k l ≠ EL i l) ∧
           a1 = mkEAction wf rfs body (EL i l) ∧
           a2 = mkEAction wf rfs body (EL j l) ∧ touches a1 a2``,
  Induct_on `l` >> simp[IN_FOLD_add_action] >> pop_assum kall_tac >>
  qx_gen_tac `h` >> eq_tac >> strip_tac >| [
    qmatch_assum_rename_tac `MEM i l` [] >>
    `∃n. n < LENGTH l ∧ i = EL n l` by metis_tac[MEM_EL] >>
    map_every qexists_tac [`0`, `SUC n`] >> simp[] >> qx_gen_tac `k` >>
    strip_tac >> `∃k0. k = SUC k0` by (Cases_on`k` >> fs[]) >> fs[] >>
    metis_tac[MEM_EL],

    qmatch_assum_rename_tac `a1 = mkEAction wf rfs body (EL i l)` [] >>
    qmatch_assum_rename_tac `a2 = mkEAction wf rfs body (EL j l)` [] >>
    map_every qexists_tac [`SUC i`, `SUC j`] >> simp[] >> qx_gen_tac `k` >>
    strip_tac >> `∃k0. k = SUC k0` by (Cases_on`k` >> fs[]) >> fs[],

    qmatch_assum_rename_tac `a1 = mkEAction wf rfs body (EL i (h::l))` [] >>
    qmatch_assum_rename_tac `a2 = mkEAction wf rfs body (EL j (h::l))` [] >>
    `i = 0 ∨ ∃i0. i = SUC i0` by (Cases_on `i` >> simp[])
    >- (`∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
        Cases_on `MEM h l`
        >- (disj2_tac >> `∃k. k < LENGTH l ∧ EL k l = h` by metis_tac[MEM_EL] >>
            qpat_assum `∀k. P k`
              (assume_tac o
               SIMP_RULE (srw_ss()) [Once arithmeticTheory.FORALL_NUM]) >>
            `k < j0` by metis_tac [DECIDE ``¬(x < y) ⇔ y ≤ x``] >>
            map_every qexists_tac [`k`, `j0`] >> simp[]) >>
        metis_tac[MEM_EL]) >>
    disj2_tac >>
    `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
    map_every qexists_tac [`i0`, `j0`] >> simp[] >>
    qpat_assum `∀k. P k`
      (ACCEPT_TAC o
       SIMP_RULE (srw_ss()) [Once arithmeticTheory.FORALL_NUM])
  ]);

val FOLDR_add_action_nodes = store_thm(
  "FOLDR_add_action_nodes",
  ``(FOLDR add_action G l).nodes = G.nodes ∪ set l``,
  simp[EXTENSION] >> Induct_on `l` >> simp[] >> metis_tac[]);

val INJ_COMPOSE_IMAGE = store_thm(
  "INJ_COMPOSE_IMAGE",
  ``INJ (f o g) s t ==> INJ f (IMAGE g s) t``,
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [INJ_THM] THEN METIS_TAC[]);

val add_action_nodes = store_thm(
  "add_action_nodes",
  ``(add_action a G).nodes = a INSERT G.nodes``,
  rw[add_action_def, ABSORPTION_RWT]);
val _ = export_rewrites ["add_action_nodes"]

val FOLDR_add_iterupd = store_thm(
  "FOLDR_add_iterupd",
  ``INJ (λa. g a.iter) (FOLDR (add_action o f) emptyG l).nodes Is ⇒
    FOLDR (add_action o (λa. a with iter updated_by g) o f) emptyG l =
    imap (λa. g a.iter) (FOLDR (add_action o f) emptyG l)``,
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Q.SPEC_THEN `(λa. g a.iter)`
    (Q.ISPEC_THEN `FOLDR (add_action o f) emptyG l`
       (Q.SPEC_THEN `f h` (mp_tac o GSYM)))
    (Q.GENL [`a`, `G`, `f`] imap_add_action) >>
  simp[] >>
  imp_res_tac (INJ_INSERT |> SPEC_ALL |> EQ_IMP_RULE |> #1
                          |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
                          |> GEN_ALL) >>
  fs[] >>
  `f h with iter := g (f h).iter = f h with iter updated_by g`
    by simp[theorem "action_component_equality"] >>
  simp[] >> disch_then match_mp_tac);

val iter_noop = prove(
  ``a with iter := a.iter = a``,
  simp[theorem "action_component_equality"]);

val imap_ID = store_thm(
  "imap_ID",
  ``imap (λa. a.iter) G = G``,
  dsimp[graph_equality, imap_edges, iter_noop]);
val _ = export_rewrites ["imap_ID"]

val imap_CONG = store_thm(
  "imap_CONG",
  ``wfG G ⇒ (∀a. a ∈ G ⇒ f a = f' a) ⇒ imap f G = imap f' G``,
  dsimp[graph_equality, imap_edges] >> csimp[] >> rpt strip_tac >>
  eq_tac >> rpt strip_tac >> metis_tac[wfG_def]);

val ALL_DISTINCT_MAP_INJ = store_thm(
  "ALL_DISTINCT_MAP_INJ",
  ``(!x y. MEM x l ∧ MEM y l ==> ((f x = f y) <=> (x = y))) ⇒
    (ALL_DISTINCT (MAP f l) <=> ALL_DISTINCT l)``,
  Induct_on `l` THEN ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP] THEN
  METIS_TAC[]);

val same_graphs = store_thm(
  "same_graphs",
  ``(∀i0 i. ddepR wf rds i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N) ⇒
    loop_to_graph (0,N) (wf o γ) (MAP (λf. f o γ) rds) (body o γ) =
      imap (λa. δ a.iter) (loop_to_graph (0,N) wf rds body)``,
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
           REWRITE_RULE[SINGL_DEF] SINGL_APPLY_PERMUTE,
           REWRITE_RULE[SINGL_DEF] SINGL_APPLY_MAP,
           MAP_MAP_o, combinTheory.o_ABS_R] >>
  pop_assum SUBST_ALL_TAC >>
  `INJ (λa. γ a.iter) (FOLDR (add_action o mk') emptyG (MAP δ [0 ..< N])).nodes
                      (count N)`
    by (dsimp[INJ_THM, IN_FOLD_add_action, MEM_MAP] >>
        simp[Abbr`mk'`, mkEAction_def] >> metis_tac[]) >>
  pop_assum (assume_tac o MATCH_MP FOLDR_add_iterupd) >>
  pop_assum SUBST_ALL_TAC >> simp[imap_imap_o] >>
  qabbrev_tac `G' = FOLDR (add_action o mk') emptyG (MAP δ [0 ..< N])` >>
  `wfG G'` by metis_tac[wfG_FOLDR_add_action] >>
  `∀a. a ∈ G' ⇒ a.iter < N`
    by (simp[Abbr`G'`, FOLDR_add_action_nodes, GSYM FOLDR_MAP_o, MEM_MAP, MAP_MAP_o] >>
        dsimp[Abbr`mk'`, mkEAction_def]) >>
  `imap (λa. δ (γ a.iter)) G' = imap (λa. a.iter) G'`
    by (ho_match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] imap_CONG) >> simp[]) >>
  simp[imap_ID] >> simp[Abbr`G'`] >>
  dsimp[graph_equality, IN_FOLD_add_action, MEM_MAP] >> conj_tac >- metis_tac[] >>
  `∀x y. mk' x = mk' y ⇔ x = y` by simp[Abbr`mk'`] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
    [FOLD_add_action_edges_ALL_DISTINCT, EL_listRangeLHI] >>
  `ALL_DISTINCT (MAP δ [0 ..< N])` by simp[MEM_listRangeLHI, ALL_DISTINCT_MAP_INJ] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
    [FOLD_add_action_edges_ALL_DISTINCT, EL_MAP, EL_listRangeLHI] >>
  map_every qx_gen_tac [`a1`, `a2`] >> eq_tac >| [
    disch_then (qx_choosel_then [`i`, `j`] strip_assume_tac) >>
    map_every qexists_tac [`γ i`, `γ j`] >> asimp[] >>
    qpat_assum `∀i0 i. ddepR wf rsf i0 i ⇒ δ i0 < δ i`
      (qspecl_then [`γ j`, `γ i`] mp_tac) >>
    simp[ddepR_def] >>
    qmatch_abbrev_tac `¬(γ j < γ i) ∨ P ⇒ γ i < γ j` >>
    `¬P`
      by (qpat_assum `touches XX YY` mp_tac >>
          simp[touches_def, Abbr`mk'`, mkEAction_def, Abbr`P`,
               REWRITE_RULE [SINGL_DEF] SINGL_APPLY_PERMUTE,
               REWRITE_RULE [SINGL_DEF] SINGL_APPLY_MAP,
               MAP_MAP_o, combinTheory.o_ABS_R] >>
          strip_tac >> simp[]) >> simp[] >>
    `i < N` by decide_tac >>
    `γ i ≠ γ j` by simp[] >> decide_tac,

    disch_then (qx_choosel_then [`i`, `j`] strip_assume_tac) >>
    map_every qexists_tac [`δ i`, `δ j`]  >> simp[] >>
    first_x_assum match_mp_tac >> simp[ddepR_def] >>
    pop_assum mp_tac >>
    simp[touches_def, Abbr`mk'`, mkEAction_def,
         REWRITE_RULE [SINGL_DEF] SINGL_APPLY_PERMUTE,
         REWRITE_RULE [SINGL_DEF] SINGL_APPLY_MAP,
         MAP_MAP_o, combinTheory.o_ABS_R]
  ]);

val FOLDR_add_actionf_nodes = store_thm(
  "FOLDR_add_actionf_nodes",
  ``(FOLDR (add_action o f) G l).nodes = { f e | MEM e l } ∪ G.nodes``,
  Induct_on `l` >> simp[EXTENSION] >> metis_tac[]);

val field_def = Define`field R = { x | (∃y. R x y) ∨ (∃y. R y x) }`

val RIMAGE_TC_IN_field = store_thm(
  "RIMAGE_TC_IN_field",
  ``∀x y. (RIMAGE f R)⁺ x y ⇒
          ∃x0 y0. x = f x0 ∧ y = f y0 ∧ x0 ∈ field R ∧ y0 ∈ field R``,
  Induct_on `(RIMAGE f R)⁺` >> simp[RIMAGE_DEF] >> rpt strip_tac
  >- (simp[field_def] >> metis_tac[]) >>
  metis_tac[]);

val INJ_RIMAGE_TC = store_thm(
  "INJ_RIMAGE_TC",
  ``INJ f (field R) SS ⇒
    ∀x y. x ∈ field R ∧ y ∈ field R ∧ (RIMAGE f R)⁺ (f x) (f y) ⇒ R⁺ x y``,
  strip_tac >>
  `∀x y. (RIMAGE f R)⁺ x y ⇒
         ∀x0 y0. x = f x0 ∧ y = f y0 ∧ x0 ∈ field R ∧ y0 ∈ field R ⇒ R⁺ x0 y0`
     suffices_by metis_tac[] >>
  Induct_on `(RIMAGE f R)⁺` >> simp[RIMAGE_DEF] >>
  rpt strip_tac
  >- (`a ∈ field R ∧ b ∈ field R` by (simp[field_def] >> metis_tac[]) >>
      metis_tac[INJ_DEF, relationTheory.TC_SUBSET]) >>
  qmatch_assum_rename_tac `(RIMAGE f R)⁺ x a` [] >>
  qmatch_assum_rename_tac `(RIMAGE f R)⁺ a y` [] >>
  `∃a0. a0 ∈ field R ∧ f a0 = a` by metis_tac[RIMAGE_TC_IN_field] >>
  metis_tac[relationTheory.TC_RULES]);

val wfG_imap = store_thm(
  "wfG_imap",
  ``wfG G ∧ INJ f G.nodes Is ⇒ wfG (imap f G)``,
  simp[wfG_def, imap_def, RIMAGE_DEF] >> strip_tac >>
  qabbrev_tac `f' = (λa. a with iter := f a)` >>
  `∀a. a with iter := f a = f' a` by simp[Abbr`f'`] >>
  simp[] >>
  `∀a1 a2. a1 ∈ G ∧ a2 ∈ G ⇒ (f' a1 = f' a2 ⇔ a1 = a2)`
    by (fs[INJ_THM,Abbr`f'`] >> simp[theorem "action_component_equality"] >>
        simp[EQ_IMP_THM]) >>
  `∀a b. (touches (f' a) b ⇔ touches a b) ∧ (touches a (f' b) ⇔ touches a b)`
    by simp[Abbr`f'`] >>
  rpt strip_tac >> simp[]
  >- metis_tac[]
  >- metis_tac[]
  >- (eq_tac >> rpt strip_tac
      >- (rw[] >> fs[] >> metis_tac[]) >>
      rw[] >> fs[] >>
      qmatch_rename_tac `D1 ∨ D2 ∨ ¬G.edges b c` ["D1", "D2"] >>
      Cases_on `G.edges b c` >> simp[] >>
      qmatch_rename_tac `f' a1 ≠ f' a2 ∨ f' a3 ≠ f' a4` [] >>
      `a1 ∈ G ∧ a2 ∈ G ∧ a3 ∈ G ∧ a4 ∈ G` by metis_tac[] >>
      simp[] >> Cases_on `a1 = a2` >> simp[] >> strip_tac >>
      rw[] >> metis_tac[]) >>
  `field G.edges ⊆ G.nodes`
    by (simp[field_def, SUBSET_DEF] >> metis_tac[]) >>
  `INJ f' (field G.edges) (IMAGE f' (field G.edges))`
    by (simp[INJ_DEF] >> map_every qx_gen_tac [`a`, `b`] >>
        strip_tac >> `a ∈ G ∧ b ∈ G` by metis_tac[SUBSET_DEF] >>
        simp[]) >>
  `∃a10 a20. a1 = f' a10 ∧ a2 = f' a20 ∧
             a10 ∈ field G.edges ∧ a20 ∈ field G.edges`
    by (match_mp_tac RIMAGE_TC_IN_field >> simp[]) >>
  `a10 ∈ G ∧ a20 ∈ G` by metis_tac[SUBSET_DEF] >>
  metis_tac[INJ_RIMAGE_TC]);

val correctness = store_thm(
  "correctness",
  ``(∀i0 i. ddepR wf rds i0 i ==> δ i0 < δ i) ∧
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
  mp_tac same_graphs >> simp[] >>
  disch_then SUBST_ALL_TAC >>
  qabbrev_tac `G = loop_to_graph (0,N) wf rds body` >>
  `INJ (λa. δ a.iter) G.nodes (count N)`
    by (simp[Abbr`G`, loop_to_graph_FOLDR,
             FOLDR_add_actionf_nodes] >>
        dsimp[INJ_DEF, mkEAction_def]) >>
  `wfG G` by metis_tac[wfG_loop_to_graph] >>
  metis_tac[imap_irrelevance, wfG_imap, wfG_evaluate_deterministically]);

val _ = export_theory();
