open HolKernel Parse boolLib bossLib;

open pred_setTheory listRangeTheory listTheory
open finite_mapTheory
open lcsymtacs
open indexedListsTheory
open actionTheory

val _ = new_theory "actionGraph";

val _ = Hol_datatype`
  action_graph0 = <|
    nodes : ('a,'acc,'ident) action set;
    edges : ('a,'acc,'ident) action -> ('a,'acc,'ident) action set
  |>
`

val wfG_def = Define`
  wfG G ⇔
      FINITE G.nodes ∧
      (∀a1 a2. G.edges a1 a2 ⇒ touches a1 a2 ∧ a1 ∈ G.nodes ∧ a2 ∈ G.nodes) ∧
      (∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ touches a1 a2 ∧ a1 ≠ a2 ⇒ (¬G.edges a1 a2 ⇔ G.edges a2 a1)) ∧
      (∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ G.edges⁺ a1 a2 ⇒ ¬G.edges⁺ a2 a1) ∧
      INJ (λa. a.ident) G.nodes univ(:'ident)
`;

val touching_actions_link0 = prove(
  ``wfG G ⇒ a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ a1 ≠ a2 ∧ a1 ∼ₜ a2 ⇒
    G.edges a1 a2 ∨ G.edges a2 a1``,
  metis_tac[wfG_def]);

val emptyG0_def = Define`
  emptyG0 = <| nodes := ∅; edges := REMPTY |>
`;

val emptyG0_nodes = prove(
  ``action_graph0_nodes emptyG0 = {}``,
  simp[emptyG0_def])

val emptyG0_edges = prove(
  ``emptyG0.edges = REMPTY``,
  simp[emptyG0_def]);

val wfG_empty = store_thm(
  "wfG_empty",
  ``wfG emptyG0``,
  simp[wfG_def, emptyG0_def, INJ_EMPTY]);

val wfEQ_def = Define`
  wfEQ g1 g2 <=> g1 = g2 ∧ wfG g1
`

val wfEQ_equiv = store_thm(
  "wfEQ_equiv",
  ``(∃g:('a,'b,'c) action_graph0. wfEQ g g) ∧
    (∀x y:('a,'b,'c) action_graph0. wfEQ x y ⇔ wfEQ x x ∧ wfEQ y y ∧ wfEQ x = wfEQ y)``,
  rw[wfEQ_def, FUN_EQ_THM] >- metis_tac[wfG_empty] >>
  rw[EQ_IMP_THM] >> simp[]);

fun simple_rsp t = prove(
  ``wfEQ g1 g2 ⇒ ^t g1 = ^t g2``,
  simp[wfEQ_def]);

val wfEQ_emptyG0 = prove(
  ``wfEQ emptyG0 emptyG0``,
  simp[wfEQ_def, wfG_empty]);

val INWR = prove(
  ``x ∈ W R <=> R x x``,
  simp[combinTheory.W_DEF]);

val wfG_irrefl = store_thm(
  "wfG_irrefl",
  ``!G. wfG G ⇒ ¬G.edges x x``,
  simp[wfG_def] >> rpt strip_tac >>
  metis_tac[relationTheory.TC_SUBSET]);

val empty_edges = prove(
  ``emptyG0.edges = REMPTY``,
  simp[emptyG0_def]);

val graph0_equality = prove(
  ``!G1 G2 :: respects wfEQ.
      wfEQ G1 G2 ⇔
      (∀a. a ∈ G1.nodes ⇔ a ∈ G2.nodes) ∧ (∀a1 a2. G1.edges a1 a2 ⇔ G2.edges a1 a2)``,
  simp[theorem "action_graph0_component_equality", Once EQ_IMP_THM, wfEQ_def, RES_FORALL_THM,
       quotientTheory.respects_def, INWR] >>
  ntac 5 strip_tac >> conj_tac >- simp[EXTENSION] >> simp[FUN_EQ_THM])

val idents0_def = Define`
  idents0 G = IMAGE (\a. a.ident) G.nodes
`;

val add_action0_def = Define`
  add_action0 a G =
    if a.ident ∈ idents0 G then G
    else
      <| nodes := a INSERT G.nodes ;
         edges := (λsrc tgt. G.edges src tgt ∨
                             src = a ∧ touches a tgt ∧ tgt ∈ G.nodes) |>
`;

val add_postaction0_def = Define`
  add_postaction0 a G =
    if a.ident ∈ idents0 G then G
    else
      <| nodes := a INSERT G.nodes ;
         edges := (λsrc tgt. G.edges src tgt ∨
                             src ∈ G.nodes ∧ touches src tgt ∧ tgt = a) |>
`;

val TC_in_R = store_thm(
  "TC_in_R",
  ``∀x y. R⁺ x y ⇒ (∃z. R x z) ∧ (∃z. R z y)``,
  Induct_on `R⁺ x y` >> metis_tac[]);

val wfG_WF = prove(
  ``!G::respects wfEQ. WF G.edges``,
  simp[wfG_def, quotientTheory.respects_def, INWR, RES_FORALL_THM, wfEQ_def] >>
  rpt strip_tac >>
  `G.edges = REL_RESTRICT G.edges G.nodes`
    by (simp[REL_RESTRICT_DEF, FUN_EQ_THM, EQ_IMP_THM] >>
        metis_tac[]) >>
  first_assum (fn th => simp[FINITE_WF_noloops, Once th]) >>
  pop_assum (SUBST_ALL_TAC o SYM) >>
  simp[relationTheory.irreflexive_def] >> metis_tac[TC_in_R]);

val wfG_FINITE = prove(
  ``wfG g ==> FINITE g.nodes``,
  simp[wfG_def]);

val wfEQ_FINITE = prove(
  ``!G::respects wfEQ. FINITE G.nodes``,
  simp[wfG_def, wfEQ_def, quotientTheory.respects_def, INWR, RES_FORALL_THM]);

val add_action0_lemma = prove(
  ``(∀a1 a2. R' a1 a2 ⇒ R a1 a2 ∨ a1 = a ∧ a2 ≠ a) ∧ (∀b. ¬R a b ∧ ¬R b a) ⇒
     ∀a1 a2. R'⁺ a1 a2 ⇒ a2 ≠ a ∧ a1 = a ∨ R⁺ a1 a2``,
  strip_tac >> Induct_on `R'⁺` >> conj_tac >- metis_tac[relationTheory.TC_SUBSET] >>
  rpt strip_tac >> simp[]
  >- metis_tac[TC_in_R]
  >- metis_tac[TC_in_R] >>
  metis_tac[relationTheory.TC_RULES]);

val wfG_add_action0 = prove(
  ``wfG G ⇒ wfG (add_action0 a G)``,
  rw[add_action0_def] >>
  qabbrev_tac `
    R' = (λsrc tgt. G.edges src tgt ∨ src = a ∧ touches a tgt ∧ tgt ∈ G.nodes)
  ` >>
  `∀x y. G.edges x y ∨ x = a ∧ touches a y ∧ y ∈ G.nodes <=> R' x y`
    by simp[Abbr`R'`] >>
  markerLib.RM_ALL_ABBREVS_TAC >> fs[wfG_def, idents0_def] >> reverse (rpt strip_tac)
  >- (fs[INJ_IFF] >> metis_tac[])
  >- (`∀b. ¬G.edges a b ∧ ¬G.edges b a` by metis_tac[] >>
      `∀a1 a2. R' a1 a2 ⇒ G.edges a1 a2 ∨ a1 = a ∧ a2 ≠ a` by metis_tac[] >>
      pop_assum
        (fn c1 => pop_assum
           (fn c2 => assume_tac (MATCH_MP add_action0_lemma (CONJ c1 c2)))) >>
      metis_tac[]) >>
  metis_tac[TC_in_R, touches_SYM])

val wfEQ_add_action0 = prove(
  ``a1 = a2 ∧ wfEQ g1 g2 ⇒ wfEQ (add_action0 a1 g1) (add_action0 a2 g2)``,
  csimp[wfEQ_def, wfG_add_action0]);

val add_postaction0_lemma = prove(
  ``(∀a1 a2. R' a1 a2 ⇒ R a1 a2 ∨ a2 = a ∧ a1 ≠ a) ∧ (∀b. ¬R a b ∧ ¬R b a) ⇒
     ∀a1 a2. R'⁺ a1 a2 ⇒ a1 ≠ a ∧ a2 = a ∨ R⁺ a1 a2``,
  strip_tac >> Induct_on `R'⁺ a1 a2` >> conj_tac
  >- metis_tac[relationTheory.TC_SUBSET] >>
  rpt strip_tac >> simp[]
  >- metis_tac[TC_in_R]
  >- metis_tac[TC_in_R] >>
  metis_tac[relationTheory.TC_RULES]);

val wfG_add_postaction0 = prove(
  ``wfG G ⇒ wfG (add_postaction0 a G)``,
  rw[add_postaction0_def] >>
  qabbrev_tac `
    R' = (λsrc tgt. G.edges src tgt ∨ src ∈ G.nodes ∧ touches src tgt ∧ tgt = a)
  ` >>
  `∀x y. G.edges x y ∨ x ∈ G.nodes ∧ touches x y ∧ y = a <=> R' x y`
    by simp[Abbr`R'`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  fs[wfG_def, idents0_def] >> reverse (rpt strip_tac)
  >- (fs[INJ_IFF] >> metis_tac[])
  >- (`∀b. ¬G.edges a b ∧ ¬G.edges b a` by metis_tac[] >>
      `∀a1 a2. R' a1 a2 ⇒ G.edges a1 a2 ∨ a2 = a ∧ a1 ≠ a`
        by metis_tac[] >>
      pop_assum (fn c1 => pop_assum
        (fn c2 => mp_tac (MATCH_MP add_postaction0_lemma (CONJ c1 c2)))) >>
      metis_tac[]) >>
  metis_tac[TC_in_R, touches_SYM]);

val wfEQ_add_postaction0 = prove(
  ``a1 = a2 ∧ wfEQ g1 g2 ⇒ wfEQ (add_postaction0 a1 g1) (add_postaction0 a2 g2)``,
  csimp[wfEQ_def, wfG_add_postaction0]);


val IN_add_action0 = prove(
  ``x ∈ (add_action0 a G).nodes <=>
    a.ident ∉ idents0 G ∧ x = a ∨ x ∈ G.nodes``,
  rw[add_action0_def]);

val IN_add_postaction0 = prove(
  ``x ∈ (add_postaction0 a G).nodes <=>
    a.ident ∉ idents0 G ∧ x = a ∨ x ∈ G.nodes``,
  rw[add_postaction0_def]);

val add_action0_edges = prove(
  ``(add_action0 a G).edges a1 a2 ⇔
      a.ident ∉ idents0 G ∧ a1 = a ∧ a2 ∈ G.nodes ∧ touches a1 a2 ∨
      G.edges a1 a2``,
  rw[add_action0_def] >> metis_tac[]);

val add_postaction0_edges = prove(
  ``(add_postaction0 a G).edges a1 a2 <=>
       a.ident ∉ idents0 G ∧ a1 ∈ G.nodes ∧ a2 = a ∧ touches a1 a2 ∨
       G.edges a1 a2``,
  rw[add_postaction0_def] >> metis_tac[]);

val fmap0_def = Define`
  fmap0 G = FUN_FMAP (λi. @a. a ∈ G.nodes ∧ a.ident = i) (idents0 G)
`;

val FDOM_fmap0 = prove(
  ``!g::respects wfEQ. FDOM (fmap0 g) = idents0 g``,
  simp[fmap0_def, FUN_FMAP_DEF, wfEQ_def, wfG_FINITE, idents0_def,
       IMAGE_FINITE, quotientTheory.respects_def, INWR]);

val fmap0_add_action0 = prove(
  ``!g::respects wfEQ.
       fmap0 (add_action0 a g) ' i = if a.ident = i ∧ i ∉ idents0 g then a
                                     else fmap0 g ' i``,
  simp[wfEQ_def, quotientTheory.respects_def, INWR, RES_FORALL_THM] >>
  rw[add_action0_def] >> fs[wfG_def, INJ_IFF, fmap0_def, idents0_def] >| [
    metis_tac[],
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    `∀b. b ∈ g.nodes ∧ b.ident = a.ident <=> F`
      suffices_by disch_then (fn th => simp[th]) >>
    metis_tac[],
    Cases_on `i ∈ IMAGE (λa. a.ident) g.nodes`
    >- (dsimp[IMAGE_FINITE, FUN_FMAP_DEF] >> csimp[]) >>
    simp[IMAGE_FINITE, NOT_FDOM_FAPPLY_FEMPTY, FUN_FMAP_DEF],
    `a.ident ≠ a'.ident` by metis_tac[] >>
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    metis_tac[]
  ]);

val fmap0_add_postaction0 = prove(
  ``!g::respects wfEQ.
       fmap0 (add_postaction0 a g) ' i =
         if a.ident = i ∧ i ∉ idents0 g then a
         else fmap0 g ' i``,
  simp[wfEQ_def, quotientTheory.respects_def, INWR, RES_FORALL_THM] >>
  rw[add_postaction0_def] >> fs[wfG_def, INJ_IFF, fmap0_def, idents0_def] >| [
    metis_tac[],
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    `∀b. b ∈ g.nodes ∧ b.ident = a.ident <=> F`
      suffices_by disch_then (fn th => simp[th]) >>
    metis_tac[],
    Cases_on `i ∈ IMAGE (λa. a.ident) g.nodes`
    >- (dsimp[IMAGE_FINITE, FUN_FMAP_DEF] >> csimp[]) >>
    simp[IMAGE_FINITE, NOT_FDOM_FAPPLY_FEMPTY, FUN_FMAP_DEF],
    `a.ident ≠ a'.ident` by metis_tac[] >>
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    metis_tac[]
  ]);

val IN_edges0 = prove(
  ``!g. wfG g ⇒
    g.edges a1 a2 ⇒ a1 ∈ g.nodes ∧ a2 ∈ g.nodes ∧
                    touches a1 a2 ∧ ¬g.edges a2 a1``,
  simp[wfG_def] >> metis_tac[relationTheory.TC_SUBSET])

val wfG_wfEQ = prove(
  ``wfG g <=> g ∈ respects wfEQ``,
  simp[quotientTheory.respects_def, INWR, wfEQ_def]);

fun mkwfeq th =
    th |> SIMP_RULE bool_ss [GSYM RES_FORALL_THM, wfG_wfEQ]

val gDELETE0_def = Define`
  gDELETE0 G a = <|
    nodes := G.nodes DELETE a;
    edges := (\a1 a2. G.edges a1 a2 ∧ a1 ≠ a ∧ a2 ≠ a)
  |>
`;

val TC_MONO' =
    relationTheory.TC_MONOTONE
      |> ONCE_REWRITE_RULE[DECIDE ``a ⇒ b ⇒ c ⇔ b ⇒ a ⇒ c``]
      |> GEN_ALL

val wfG_delete = prove(
  ``!g. wfG g ⇒ wfG (gDELETE0 g a)``,
  simp[gDELETE0_def, wfG_def, INJ_IFF] >> reverse (rpt strip_tac)
  >- (`g.edges⁺ a1 a2 ∧ g.edges⁺ a2 a1` suffices_by metis_tac[] >>
      conj_tac >>
      first_x_assum (MATCH_MP_TAC o MATCH_MP TC_MONO') >> simp[]) >>
  metis_tac[]);

val wfEQ_delete = prove(
  ``wfEQ g1 g2 ⇒ wfEQ (gDELETE0 g1 b) (gDELETE0 g2 b)``,
  simp[wfEQ_def, wfG_delete]);

val nodes_delete = prove(
  ``(gDELETE0 g a).nodes = g.nodes DELETE a``,
  simp[gDELETE0_def]);

val IN_gDELETE0 = prove(
  ``a ∈ (gDELETE0 G b).nodes ⇔ a ∈ G.nodes ∧ a ≠ b``,
  simp[nodes_delete]);

val gDELETE0_edges = prove(
  ``(gDELETE0 G a).edges b c ⇔ G.edges b c ∧ a ≠ b ∧ a ≠ c``,
  simp[gDELETE0_def] >> metis_tac[]);

val gDELETE0_commutes = prove(
  ``gDELETE0 (gDELETE0 G a1) a2 = gDELETE0 (gDELETE0 G a2) a1``,
  simp[gDELETE0_def, theorem "action_graph0_component_equality", DELETE_COMM] >>
  simp[FUN_EQ_THM] >> metis_tac[]);

val RIMAGE_DEF = new_definition(
  "RIMAGE_DEF",
  ``RIMAGE f R x y <=> ?a b. (x = f a) /\ (y = f b) /\ R a b``);

val RIMAGE_REMPTY = store_thm(
  "RIMAGE_REMPTY",
  ``RIMAGE f REMPTY = REMPTY``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, RIMAGE_DEF]);
val _ = export_rewrites ["RIMAGE_REMPTY"]

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
  qmatch_assum_rename_tac `(RIMAGE f R)⁺ x a` >>
  qmatch_assum_rename_tac `(RIMAGE f R)⁺ a y` >>
  `∃a0. a0 ∈ field R ∧ f a0 = a` by metis_tac[RIMAGE_TC_IN_field] >>
  metis_tac[relationTheory.TC_RULES]);


val imap0_def = Define`
  imap0 f G = if INJ f (idents0 G) UNIV then
                G with <| nodes updated_by IMAGE (λa. a with ident updated_by f);
                          edges updated_by RIMAGE (λa. a with ident updated_by f)
                       |>
              else G
`;

val imap0_id = prove(
  ``¬INJ f (idents0 G) UNIV ⇒ imap0 f G = G``,
  simp[imap0_def]);

val wfG_imap = prove(
  ``wfG G ⇒ wfG (imap0 f G)``,
  simp[imap0_def, idents0_def] >> COND_CASES_TAC >> simp[] >>
  simp[wfG_def, RIMAGE_DEF] >> strip_tac >>
  qabbrev_tac `f' = λa. a with ident updated_by f` >> simp[] >>
  `∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ⇒ (f' a1 = f' a2 ⇔ a1 = a2)`
    by (rpt strip_tac >> simp[action_component_equality, Abbr`f'`] >>
        full_simp_tac (srw_ss() ++ boolSimps.DNF_ss) [INJ_IFF]) >>
  `∀a b. (f' a ∼ₜ b ⇔ a ∼ₜ b) ∧ (a ∼ₜ f' b ⇔ a ∼ₜ b)`
    by simp[Abbr`f'`] >> rw[]
  >- rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (eq_tac >- (fs[] >> metis_tac[]) >>
      disch_then (qx_choosel_then [`b`, `c`] strip_assume_tac) >>
      map_every qx_gen_tac [`d`, `e`] >> fs[] >> Cases_on `G.edges d e` >>
      simp[] >>
      `b ∈ G.nodes ∧ c ∈ G.nodes ∧ d ∈ G.nodes ∧ e ∈ G.nodes` by metis_tac[] >>
      simp[] >> metis_tac[])
  >- (`field G.edges ⊆ G.nodes`
        by (simp[field_def, SUBSET_DEF] >> metis_tac[]) >>
      `INJ f' (field G.edges) (IMAGE f' (field G.edges))`
        by (simp[INJ_DEF] >> map_every qx_gen_tac [`c`, `d`] >>
            strip_tac >> `c ∈ G.nodes ∧ d ∈ G.nodes` by metis_tac[SUBSET_DEF] >>
            simp[]) >>
      IMP_RES_THEN (qx_choosel_then [`c`, `d`] strip_assume_tac)
         RIMAGE_TC_IN_field >>
      `a = c ∧ a' = d` by metis_tac[SUBSET_DEF] >> rw[] >>
      metis_tac[INJ_RIMAGE_TC]) >>
  full_simp_tac (srw_ss() ++ boolSimps.DNF_ss)[INJ_IFF, Abbr`f'`])

val wfEQ_imap0 = prove(
  ``wfEQ g1 g2 ⇒ wfEQ (imap0 f g1) (imap0 f g2)``,
  csimp[wfEQ_def, wfG_imap]);

val imap_emptyG0 = prove(
  ``imap0 f emptyG0 = emptyG0``,
  simp[emptyG0_def, imap0_def]);

val IN_imap0 = prove(
  ``INJ f (idents0 G) UNIV ⇒ (a ∈ (imap0 f G).nodes ⇔ ∃a0. a0 ∈ G.nodes ∧ a = a0 with ident updated_by f)``,
  simp[imap0_def] >> metis_tac[]);

val imap0_edges = prove(
  ``INJ f (idents0 G) UNIV ⇒
    ((imap0 f G).edges a1 a2 ⇔
      ∃a10 a20. G.edges a10 a20 ∧ a1 = a10 with ident updated_by f ∧
                a2 = a20 with ident updated_by f)``,
  simp[imap0_def, RIMAGE_DEF] >> metis_tac[]);

val iter0_11 = prove(
  ``∀g. wfG g ⇒ INJ (λa. a.ident) g.nodes UNIV``,
  simp[wfG_def]);

val frange_fmap0 = prove(
  ``∀g. wfG g ⇒ FRANGE (fmap0 g) = g.nodes``,
  simp[fmap0_def, FRANGE_FMAP, idents0_def, IMAGE_FINITE, wfG_FINITE,
       GSYM IMAGE_COMPOSE, combinTheory.o_ABS_R] >>
  simp[EXTENSION, EQ_IMP_THM] >> rw[]
  >- (SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >> simp[]) >>
  qexists_tac `x` >>
  imp_res_tac iter0_11 >> fs[INJ_IFF] >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >> metis_tac[])

val fmap0_inverts_ident = prove(
  ``∀(g::respects wfEQ). ∀a. a ∈ g.nodes ⇒ fmap0 g ' a.ident = a``,
  simp[fmap0_def, idents0_def, FUN_FMAP_DEF, IMAGE_FINITE, wfG_FINITE,
       wfEQ_def, RES_FORALL_THM, quotientTheory.IN_RESPECTS] >>
  rpt strip_tac >> SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  fs[wfG_def, INJ_IFF] >> metis_tac[]);

val dgmap0_def = Define`
  dgmap0 f g  =
    <| nodes := IMAGE (polydata_upd f) g.nodes;
       edges := RIMAGE (polydata_upd f) g.edges
    |>
`;

val touches_dataupd = store_thm(
  "touches_dataupd[simp]",
  ``(polydata_upd f a ∼ₜ b ⇔ a ∼ₜ b) ∧
    (b ∼ₜ polydata_upd f a ⇔ b ∼ₜ a)``,
  simp[touches_def, polydata_upd_def]);

val dataupd_equality = store_thm(
  "dataupd_equality",
  ``wfG g ∧ a ∈ g.nodes ∧ b ∈ g.nodes ⇒
    (polydata_upd f a = polydata_upd f b ⇔ a = b)``,
  strip_tac >> eq_tac >> simp[polydata_upd_def] >> simp[action_component_equality] >>
  fs[wfG_def, INJ_IFF]);

val TC_RIMAGE_dataupd0 = prove(
  ``∀a b.
      (RIMAGE (polydata_upd f) g.edges)⁺ a b ⇒
      wfG g ⇒
      ∀a0 b0. a0 ∈ g.nodes ∧ b0 ∈ g.nodes ∧
              a = polydata_upd f a0 ∧
              b = polydata_upd f b0  ⇒
              g.edges⁺ a0 b0``,
  ho_match_mp_tac relationTheory.TC_STRONG_INDUCT_LEFT1 >> rpt conj_tac
  >- (simp[PULL_FORALL] >> simp[RIMAGE_DEF, PULL_EXISTS] >> rpt strip_tac >>
      metis_tac[dataupd_equality, wfG_def, relationTheory.TC_SUBSET]) >>
  map_every qx_gen_tac [`a`, `a'`, `b`] >> rpt strip_tac >> fs[] >>
  fs[RIMAGE_DEF] >> rw[] >>
  `a0 = a''` by metis_tac[dataupd_equality, wfG_def] >> rw[] >>
  metis_tac[relationTheory.TC_RULES, wfG_def]);

val TC_RIMAGE_dataupd = SIMP_RULE (srw_ss()) [PULL_FORALL] TC_RIMAGE_dataupd0

val wfG_dgmap = store_thm(
  "wfG_dgmap",
  ``wfG g ⇒ wfG (dgmap0 f g)``,
  strip_tac >> `∀x. ¬g.edges x x` by metis_tac[wfG_irrefl] >>
  `∀a b f. a ∈ g.nodes ∧ b ∈ g.nodes ⇒
           (polydata_upd f a = polydata_upd f b ⇔ a = b)`
    by metis_tac[dataupd_equality] >>
  simp[wfG_def, dgmap0_def, PULL_EXISTS] >> rpt strip_tac
  >- fs[wfG_def]
  >- (fs[RIMAGE_DEF, wfG_def] >> metis_tac[])
  >- (simp[RIMAGE_DEF, GSYM IMP_DISJ_THM] >> eq_tac >> strip_tac >> fs[wfG_def]
      >- metis_tac[] >>
      qmatch_assum_rename_tac `g.edges a1 a2` >>
      map_every qx_gen_tac [`a3`, `a4`] >> rpt strip_tac >>
      `a1 ∈ g.nodes ∧ a2 ∈g.nodes ∧ a3 ∈ g.nodes ∧ a4 ∈ g.nodes` by metis_tac[] >>
      rpt (first_x_assum (mp_tac o assert (is_eq o concl))) >> simp[] >>
      rpt strip_tac >> rw[] >> metis_tac[])
  >- metis_tac[wfG_def, TC_RIMAGE_dataupd] >>
  fs[wfG_def, INJ_IFF, PULL_EXISTS, polydata_upd_def]);

val wfEQ_dgmap0 = prove(
  ``wfEQ g1 g2 ⇒ wfEQ (dgmap0 f g1) (dgmap0 f g2)``,
  csimp[wfEQ_def, wfG_dgmap]);

val dgmap0_emptyG = prove(
  ``dgmap0 f emptyG0 = emptyG0``,
  simp[emptyG0_def, dgmap0_def]);

val IN_dgmap0 = prove(
  ``a ∈ (dgmap0 f G).nodes ⇔ ∃a0. a0 ∈ G.nodes ∧ a = polydata_upd f a0``,
  simp[dgmap0_def] >> metis_tac[]);

val dgmap0_edges = prove(
  ``(dgmap0 f G).edges a1 a2 ⇔
    ∃a10 a20. G.edges a10 a20 ∧ a1 = polydata_upd f a10 ∧
              a2 = polydata_upd f a20``,
  simp[dgmap0_def, RIMAGE_DEF] >> metis_tac[]);

fun define_quotient {types,defs,thms,poly_preserves,poly_respects,respects} =
    let
      fun mk(s,t) = {def_name = s ^ "_def", fname = s, fixity = NONE, func = t}
      val (names, old_thms) = ListPair.unzip thms
      val new_thms =
          quotientLib.define_quotient_types_full {
            types = types, defs = map mk defs, old_thms = old_thms,
            poly_respects = poly_respects, poly_preserves = poly_preserves,
            respects = respects, tyop_equivs = [],
            tyop_quotients = [], tyop_simps = []}
      val named_new = ListPair.zip(names, new_thms)
    in
      map save_thm named_new
    end

val [emptyG_nodes, emptyG_edges, edges_irrefl, graph_equality,
     edges_WF, nodes_FINITE, IN_add_action, add_action_edges,
     IN_add_postaction, add_postaction_edges,
     idents_thm, FDOM_fmap,
     fmap_add_action, fmap_add_postaction,
     IN_edges,
     IN_gDELETE, nodes_gDELETE, gDELETE_edges, gDELETE_commutes,
     imap_emptyG, IN_imap, imap_edges, touching_actions_link, imap_id,
     ident_INJ, frange_fmap, fmap_inverts_ident,
     dgmap_edges, dgmap_emptyG, IN_dgmap] =
define_quotient {
  types = [{name = "action_graph", equiv = wfEQ_equiv}],
  defs = [("emptyG",``emptyG0``),
          ("idents", ``idents0``),
          ("ag_nodes", ``action_graph0_nodes``),
          ("ag_edges", ``action_graph0_edges``),
          ("add_action", ``add_action0``),
          ("add_postaction", ``add_postaction0``),
          ("fmap", ``fmap0``),
          ("gDELETE", ``gDELETE0``),
          ("imap", ``imap0``),
          ("dgmap", ``dgmap0``)],
  thms = [("emptyG_nodes", emptyG0_nodes),
          ("emptyG_edges", emptyG0_edges),
          ("edges_irrefl", mkwfeq wfG_irrefl),
          ("graph_equality", graph0_equality),
          ("edges_WF", wfG_WF),
          ("nodes_FINITE", mkwfeq (GEN_ALL wfG_FINITE)),
          ("IN_add_action", IN_add_action0),
          ("add_action_edges", add_action0_edges),
          ("IN_add_postaction", IN_add_postaction0),
          ("add_postaction_edges", add_postaction0_edges),
          ("idents_thm", idents0_def),
          ("FDOM_fmap", FDOM_fmap0),
          ("fmap_add_action", fmap0_add_action0),
          ("fmap_add_postaction", fmap0_add_postaction0),
          ("IN_edges", mkwfeq IN_edges0),
          ("IN_gDELETE", mkwfeq IN_gDELETE0),
          ("nodes_gDELETE", nodes_delete),
          ("gDELETE_edges", gDELETE0_edges),
          ("gDELETE_commutes", gDELETE0_commutes),
          ("imap_emptyG", imap_emptyG0),
          ("IN_imap", IN_imap0),
          ("imap_edges", imap0_edges),
          ("touching_actions_link", mkwfeq (GEN_ALL touching_actions_link0)),
          ("imap_id", imap0_id),
          ("ident_INJ", mkwfeq (iter0_11)),
          ("frange_fmap", mkwfeq (frange_fmap0)),
          ("fmap_inverts_ident", fmap0_inverts_ident),
          ("dgmap_edges", dgmap0_edges),
          ("dgmap_emptyG", dgmap0_emptyG),
          ("IN_dgmap", IN_dgmap0)
         ],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfEQ_emptyG0, simple_rsp ``action_graph0_nodes``,
              simple_rsp ``action_graph0_edges``,
              simple_rsp ``fmap0``, wfEQ_delete,
              simple_rsp ``idents0``, wfEQ_add_action0,
              wfEQ_add_postaction0,
              wfEQ_imap0, wfEQ_dgmap0]}

val _ = overload_on("ag_edge_arrow", ``\x g y. ag_edges g x y``)
val _ = overload_on("not_ag_edge_arrow", ``\x g y. ¬ag_edges g x y``)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "-<", TM, TOK ">->",
                                 BreakSpace(1,2)],
                  term_name = "ag_edge_arrow"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "-<", TM, TOK ">/->",
                                 BreakSpace(1,2)],
                  term_name = "not_ag_edge_arrow"}

val _ = set_mapped_fixity {fixity = Infixl 500, term_name = "add_action",
                           tok = "⊕"}

val _ = overload_on ("\\\\", ``gDELETE``)

val _ = overload_on ("IN", ``\a g. a IN ag_nodes g``)
val _ = overload_on ("NOTIN", ``\a g. ~(a IN ag_nodes g)``)

val _ = export_rewrites ["edges_WF", "IN_add_action", "IN_add_postaction",
                         "IN_imap", "emptyG_nodes", "imap_emptyG",
                         "emptyG_edges", "nodes_gDELETE", "nodes_FINITE",
                         "gDELETE_edges", "edges_irrefl", "dgmap_emptyG"]

val gtouches_def = Define`
  gtouches (g1:(α,β,γ)action_graph) (g2:(α,β,γ)action_graph) ⇔
    ∃a1 a2. a1 ∈ g1 ∧ a2 ∈ g2 ∧ touches a1 a2
`;

val gtouches_empty = store_thm(
  "gtouches_empty[simp]",
  ``(gtouches emptyG g ⇔ F) ∧ (gtouches g emptyG ⇔ F)``,
  simp[gtouches_def]);

val gtouches_add_action = store_thm(
  "gtouches_add_action[simp]",
  ``(gtouches (a ⊕ g1) g2 ⇔
       a.ident ∉ idents g1 ∧ (∃b. b ∈ g2 ∧ touches a b) ∨ gtouches g1 g2) ∧
    (gtouches g1 (a ⊕ g2) ⇔
       a.ident ∉ idents g2 ∧ (∃b. b ∈ g1 ∧ touches b a) ∨ gtouches g1 g2)``,
  simp[gtouches_def] >> metis_tac[]);

val gtouches_SYM = store_thm(
  "gtouches_SYM",
  ``gtouches g1 g2 ⇒ gtouches g2 g1``,
  metis_tac[gtouches_def, touches_SYM]);

val _ = set_fixity "∼ᵍ" (Infix(NONASSOC, 450))
val _ = overload_on("∼ᵍ", ``gtouches``)

val idents_add_action = store_thm(
  "idents_add_action[simp]",
  ``idents (add_action a G) = a.ident INSERT idents G``,
  dsimp[idents_thm, EXTENSION, EQ_IMP_THM] >> metis_tac[]);

val idents_add_postaction = store_thm(
  "idents_add_postaction[simp]",
  ``idents (add_postaction a G) = a.ident INSERT idents G``,
  dsimp[idents_thm, EXTENSION, EQ_IMP_THM] >> metis_tac[]);

val FINITE_idents = store_thm(
  "FINITE_idents[simp]",
  ``FINITE (idents g)``,
  simp[idents_thm]);

val add_postactionID = store_thm(
  "add_postactionID",
  ``a.ident ∈ idents g ⇒ add_postaction a g = g``,
  simp[graph_equality, add_postaction_edges]);

val idents_emptyG = store_thm(
  "idents_emptyG[simp]",
  ``idents emptyG = ∅``,
  simp[idents_thm]);

val ident_11 = store_thm(
  "ident_11",
  ``a1 ∈ G ∧ a2 ∈ G ⇒ (a1.ident = a2.ident ⇔ a1 = a2)``,
  metis_tac[ident_INJ, INJ_IFF]);

val add_action_EQ_emptyG = store_thm(
  "add_action_EQ_emptyG[simp]",
  ``add_action a G ≠ emptyG``,
  disch_then (mp_tac o Q.AP_TERM `idents`) >> simp[]);

val nonempty_wfG_has_points = store_thm(
  "nonempty_wfG_has_points",
  ``ag_nodes G ≠ ∅ ⇒ ∃e. e ∈ G ∧ ∀e'. e' ∈ G ⇒ e' -<G>/-> e``,
  rpt strip_tac >>
  `WF (ag_edges G)` by simp[] >>
  pop_assum mp_tac >> REWRITE_TAC [relationTheory.WF_DEF] >>
  simp[IN_DEF] >>
  pop_assum mp_tac >> simp[GSYM MEMBER_NOT_EMPTY, IN_DEF] >>
  metis_tac[]);

val _ = overload_on ("gCARD", ``\g. CARD (ag_nodes g)``)

val gcard_lemma = prove(
  ``gCARD G = 0 ⇔ G = emptyG``,
  simp[EQ_IMP_THM] >> rpt strip_tac >> fs[] >>
  simp[graph_equality] >> fs[CARD_EQ_0] >>
  metis_tac[IN_edges, NOT_IN_EMPTY]);

val gCARD_EQ_0 = save_thm(
  "gCARD_EQ_0[simp]",
  CONJ gcard_lemma (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) gcard_lemma))

val gCARD_gDELETE = store_thm(
  "gCARD_gDELETE[simp]",
  ``a ∈ G ⇒ gCARD (G \\ a) = gCARD G - 1``,
  simp[]);

val IN_emptyG = store_thm(
  "IN_emptyG",
  ``a ∈ emptyG ⇔ F``,
  simp[]);

val graph_ind = store_thm(
  "graph_ind",
  ``∀P. P emptyG ∧ (∀a g. P g ∧ a ∉ g ∧ a.ident ∉ idents g ⇒ P (a ⊕ g)) ⇒
        ∀g. P g``,
  rpt strip_tac >>
  Induct_on `gCARD g` >> simp[] >> rpt strip_tac >>
  `ag_nodes g ≠ ∅` by (strip_tac >> fs[]) >>
  `∃a. a ∈ g ∧ ∀b. b -<g>/-> a`
     by metis_tac[nonempty_wfG_has_points, IN_edges] >>
  qmatch_assum_rename_tac `SUC n = gCARD g` >>
  `gCARD (g \\ a) = n` by simp[gCARD_gDELETE] >>
  `a ⊕ (g \\ a) = g`
    by (dsimp[graph_equality, idents_thm, gDELETE_edges,
              add_action_edges] >> conj_tac
        >- metis_tac[ident_11] >>
        dsimp[EQ_IMP_THM] >> rpt strip_tac
        >- metis_tac[touching_actions_link] >>
        qmatch_assum_rename_tac `a1 -<g>-> a2` >>
        `a ≠ a2` by metis_tac[] >> simp[] >>
        Cases_on `a = a1` >> simp[] >>
        metis_tac[IN_edges, ident_11]) >>
  `a.ident ∉ idents (g \\ a)`
    by (dsimp[idents_thm] >> metis_tac[ident_11]) >>
  `P (g \\ a)` by metis_tac[] >>
  `a ∉ g \\ a` by simp[] >>
  `P (a ⊕ g \\ a)` by metis_tac[] >>
  metis_tac[]);

val add_postaction_EQ_add_action = store_thm(
  "add_postaction_EQ_add_action",
  ``∀g. (∀b. b ∈ g ⇒ ¬touches a b) ⇒ add_postaction a g = a ⊕ g``,
  simp[graph_equality, add_postaction_edges, add_action_edges, EQ_IMP_THM] >>
  rpt strip_tac >> simp[] >> rw[] >> metis_tac[touches_SYM]);

val add_postaction_empty = store_thm(
  "add_postaction_empty[simp]",
  ``add_postaction a emptyG = a ⊕ emptyG``,
  simp[graph_equality, add_postaction_edges, add_action_edges]);

val add_action_add_postaction_ASSOC = store_thm(
  "add_action_add_postaction_ASSOC",
  ``a.ident ≠ b.ident ⇒
    add_postaction b (a ⊕ g) = a ⊕ (add_postaction b g)``,
  dsimp[graph_equality, IN_add_postaction, add_postaction_edges,
        add_action_edges, idents_thm] >> metis_tac[]);

val ilink_def = Define`
  ilink i G j <=> i ∈ idents G ∧ j ∈ idents G ∧
                  fmap G ' i -<G>-> fmap G ' j
`;

val _ = overload_on ("'", ``\G i. fmap G ' i``)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "-<", TM, TOK ">#->",
                                 BreakSpace(1,2)],
                  term_name = "ilink"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "-<", TM, TOK ">/#->",
                                 BreakSpace(1,2)],
                  term_name = "not_ilink"}

val _ = overload_on ("not_ilink", ``λi G j. ¬ilink i G j``)




val wave_defn = with_flag(allow_schema_definition,true) (Hol_defn "wave") `
  wave i = MAX_SET (IMAGE (λj. wave j + 1) { j | ilink j G i })
`


val (wave_def, wave_ind) = Defn.tprove(
  wave_defn,
  reverse (WF_REL_TAC `\i j. ilink i G j`) >> simp[] >>
  simp[ilink_def] >> match_mp_tac relationTheory.WF_SUBSET >>
  qexists_tac `\i j. fmap G ' i -<G>-> fmap G ' j` >>
  simp[] >> qmatch_abbrev_tac `WF R` >>
  `R = inv_image (ag_edges G) (\i. fmap G ' i)`
    suffices_by simp[relationTheory.WF_inv_image] >>
  simp[Abbr`R`, relationTheory.inv_image_def])

val wave_thm = store_thm(
  "wave_thm",
  ``wave G i = MAX_SET { wave G j + 1 | j | j -<G>#-> i }``,
  simp[SimpLHS, Once wave_def] >> AP_TERM_TAC >>
  simp[EXTENSION]);

(* About fmap *)

val fmap_ONTO = store_thm(
  "fmap_ONTO",
  ``∀a. a ∈ G ⇒ ∃i. fmap G ' i = a``,
  rpt strip_tac >>
  `a ∈ FRANGE (fmap G)` by metis_tac[frange_fmap] >>
  `∃i. FLOOKUP (fmap G) i = SOME a` by metis_tac[FRANGE_FLOOKUP] >>
  fs[FLOOKUP_DEF] >> metis_tac[]);

val fmap_11 = store_thm(
  "fmap_11",
  ``∀i j.
     i ∈ idents g ∧ j ∈ idents g ⇒ (fmap g ' i = fmap g ' j ⇔ i = j)``,
  simp[EQ_IMP_THM] >> rpt strip_tac >> fs[idents_thm] >> rw[] >>
  pop_assum mp_tac >> simp[fmap_inverts_ident]);

val BIJ_idents_nodes = store_thm(
  "BIJ_idents_nodes",
  ``BIJ (λa. a.ident) (ag_nodes g) (idents g)``,
  simp[BIJ_IFF_INV] >> conj_tac >- simp[idents_thm] >>
  qexists_tac `FAPPLY (fmap g)` >> rpt strip_tac >>
  fs[idents_thm, fmap_inverts_ident]);

val dgmap_add_action = store_thm(
  "dgmap_add_action[simp]",
  ``dgmap f (a ⊕ g) = polydata_upd f a ⊕ dgmap f g``,
  simp[graph_equality, IN_dgmap, dgmap_edges, idents_thm, IN_add_action,
       add_action_edges, GSYM IMP_DISJ_THM, PULL_FORALL] >>
  rpt strip_tac >> eq_tac >> strip_tac >> simp[] >> TRY (metis_tac[]) >>
  dsimp[] >> fs[FORALL_AND_THM] >> simp[polydata_upd_def] >> rw[] >>
  fs[]>> metis_tac[]);

val idents_dgmap = store_thm(
  "idents_dgmap[simp]",
  ``∀g. idents (dgmap f g) = idents g``,
  ho_match_mp_tac graph_ind >> simp[]);

val fmap_dgmap = store_thm(
  "fmap_dgmap[simp]",
  ``∀g i. i ∈ idents g ⇒ (dgmap f g ' i) = polydata_upd f (g ' i)``,
  ho_match_mp_tac graph_ind >> simp[fmap_add_action] >> rw[] >> simp[]);

val ilink_emptyG = store_thm(
  "ilink_emptyG[simp]",
  ``i -<emptyG>#-> j ⇔ F``,
  simp[ilink_def]);

val ident_IN_idents = prove(
  ``a ∈ g ⇒ a.ident ∈ idents g``,
  simp[idents_thm]);

val ilink_add_action = store_thm(
  "ilink_add_action",
  ``i -<a ⊕ g>#-> j ⇔
      j ∈ idents g ∧ a.ident = i ∧ i ∉ idents g ∧ a ∼ₜ g ' j ∨ i -<g>#-> j``,
  dsimp[ilink_def, fmap_add_action, add_action_edges] >> csimp[] >>
  Cases_on `i = a.ident` >> simp[] >> csimp[ident_IN_idents] >>
  Cases_on `j ∈ idents g` >> simp[] >> Cases_on `a.ident ∈ idents g` >> simp[] >| [
    fs[idents_thm] >> metis_tac[IN_edges, fmap_inverts_ident],
    Cases_on `i ∈ idents g` >> simp[] >> eq_tac >> strip_tac >> simp[],
    Cases_on `i ∈ idents g` >> simp[] >> eq_tac >> strip_tac >> simp[]
      >- metis_tac[fmap_inverts_ident, fmap_ONTO] >>
    fs[idents_thm] >> rw[] >> metis_tac[fmap_inverts_ident],
    metis_tac[],
    fs[idents_thm] >> metis_tac[IN_edges]
  ]);

val graph_ident_equality = store_thm(
  "graph_ident_equality",
  ``(g1 = g2) ⇔ idents g1 = idents g2 ∧ (∀i. i ∈ idents g1 ⇒ g1 ' i = g2 ' i) ∧
                 (∀i j. i -<g1>#-> j ⇔ i -<g2>#-> j)``,
  simp[graph_equality, ilink_def, idents_thm] >> eq_tac >> rpt strip_tac
  >- (AP_TERM_TAC >> simp[EXTENSION])
  >- metis_tac[fmap_inverts_ident]
  >- (simp[] >> metis_tac[fmap_inverts_ident])
  >- (`ag_nodes g1 = ag_nodes g2` suffices_by simp[] >>
      qpat_assum `IMAGE ff ss = tt` mp_tac >>
      simp[EXTENSION] >> metis_tac[fmap_inverts_ident])
  >- (eq_tac >> strip_tac >> metis_tac[IN_edges, fmap_inverts_ident]))

val fmapped_ident = store_thm(
  "fmapped_ident[simp]",
  ``i ∈ idents g ⇒ (g ' i).ident = i``,
  simp[idents_thm] >> metis_tac[fmap_inverts_ident]);

val dgmap_ilink = store_thm(
  "dgmap_ilink[simp]",
  ``∀g. i -<dgmap f g>#-> j ⇔ i -<g>#-> j``,
  ho_match_mp_tac graph_ind >> simp[ilink_add_action] >> rpt strip_tac >>
  csimp[]);

val dgmap_dgmap = store_thm(
  "dgmap_dgmap[simp]",
  ``∀G. dgmap f (dgmap g G) = dgmap (f o g) G``,
  ho_match_mp_tac graph_ind >> simp[polydata_upd_def]);

val dgmap_I = store_thm(
  "dgmap_I[simp]",
  ``∀g. dgmap (λx. x) g = g ∧ dgmap I g = g``,
  ho_match_mp_tac graph_ind >> simp[polydata_upd_def] >>
  simp[FORALL_action]);

val dgmap_CONG = store_thm(
  "dgmap_CONG",
  ``∀g1 g2 f1 f2.
      (∀d. d ∈ IMAGE action_data (ag_nodes g1) ⇒ f1 d = f2 d) ∧ g1 = g2 ⇒
      dgmap f1 g1 = dgmap f2 g2``,
  simp[PULL_EXISTS] >> rpt gen_tac >> qid_spec_tac `g2` >>
  ho_match_mp_tac graph_ind >> dsimp[polydata_upd_def]);

(* ----------------------------------------------------------------------
    Properties of imap
   ---------------------------------------------------------------------- *)

val idents_imap = store_thm(
  "idents_imap",
  ``INJ f (idents G) UNIV ⇒
    idents (imap f G) = IMAGE f (idents G)``,
  dsimp[idents_thm, EXTENSION]);

val add_action_id = store_thm(
  "add_action_id",
  ``add_action a G = G ⇔ a.ident ∈ idents G ``,
  reverse eq_tac >- simp[graph_equality, add_action_edges] >>
  disch_then (mp_tac o Q.AP_TERM `λg. a ∈ g`) >> simp[] >>
  simp[idents_thm] >> metis_tac[]);

val fds = full_simp_tac (srw_ss() ++ boolSimps.DNF_ss)
val imap_add_action = store_thm(
  "imap_add_action",
  ``INJ f (a.ident INSERT idents G) UNIV ⇒
    (imap f (add_action a G) =
     add_action (a with ident updated_by f) (imap f G))``,
  strip_tac >>
  `INJ f (idents G) UNIV` by metis_tac[INJ_INSERT] >>
  Cases_on `a.ident ∈ idents G`
  >- (`add_action a G = G` by simp[graph_equality, add_action_edges] >>
      simp[add_action_id, idents_imap]) >>
  simp[graph_equality, imap_edges, IN_imap, idents_imap, imap_edges,
       add_action_edges] >> dsimp[] >> rpt strip_tac
  >- (fs[INJ_IFF] >> metis_tac[]) >>
  `∀a1 a2. (a1 = a ∨ a1 ∈ G) ∧ (a2 = a ∨ a2 ∈ G) ⇒
           (a1 with ident updated_by f = a2 with ident updated_by f ⇔
            a1 = a2)`
    by (simp[EQ_IMP_THM] >> fds [INJ_IFF, idents_thm] >>
        simp[action_component_equality]) >>
  eq_tac >> rpt strip_tac
  >- (csimp[] >> disj1_tac >> spose_not_then strip_assume_tac >>
      qpat_assum `f XX = f YY` mp_tac >> fds [INJ_IFF, idents_thm] >>
      metis_tac[])
  >- metis_tac[]
  >- (csimp[] >> rw[] >> fs[]) >>
  metis_tac[]);

val INJ_COMPOSE2 = prove(
  ``INJ (f o g) s UNIV ⇒ INJ g s UNIV ∧ INJ f (IMAGE g s) UNIV``,
  dsimp[INJ_IFF] >> metis_tac[]);

val imap_imap_o = store_thm(
  "imap_imap_o",
  ``INJ (f o g) (idents G) UNIV ⇒ imap f (imap g G) = imap (f o g) G``,
  strip_tac >> imp_res_tac INJ_COMPOSE2 >>
  dsimp[graph_equality, IN_imap, imap_edges, idents_imap]);

val ident_noop = prove(
  ``a with ident updated_by (λn. n) = a``,
  simp[action_component_equality]);

val INJ_ID_UNIV = prove(
  ``INJ (\x. x) s UNIV``,
  simp[INJ_IFF]);

val imap_ID = store_thm(
  "imap_ID[simp]",
  ``imap (λn. n) G = G``,
  dsimp[graph_equality, imap_edges, INJ_ID_UNIV, ident_noop]);

val imap_CONG = store_thm(
  "imap_CONG",
  ``G = G' ⇒ (∀a. a ∈ idents G' ⇒ f a = f' a) ⇒
    imap f G = imap f' G'``,
  rpt strip_tac >> rw[] >> Cases_on `INJ f (idents G) UNIV`
  >- (`∀a. a ∈ G ⇒ a with ident updated_by f = a with ident updated_by f'`
        by (fds[idents_thm] >> rpt strip_tac >>
            simp[action_component_equality]) >>
      `INJ f' (idents G) UNIV` by (fs[INJ_IFF] >> metis_tac[]) >>
      dsimp[graph_equality, imap_edges] >> csimp[] >> rpt strip_tac >>
      eq_tac >> rpt strip_tac >> csimp[] >> metis_tac[IN_edges]) >>
  `¬INJ f' (idents G) UNIV` by (fs[INJ_IFF] >> metis_tac[]) >>
  simp[imap_id]);

val imap_add_postaction = store_thm(
  "imap_add_postaction",
  ``INJ f (a.ident INSERT idents g) UNIV ⇒
    imap f (add_postaction a g) =
        add_postaction (a with ident updated_by f) (imap f g)``,
  map_every qid_spec_tac [`a`, `g`] >> ho_match_mp_tac graph_ind >>
  simp[imap_add_action] >> map_every qx_gen_tac [`a`, `g`] >>
  strip_tac >> qx_gen_tac `b` >> strip_tac >>
  `INJ f (a.ident INSERT idents g) UNIV` by fs[INJ_INSERT] >>
  `INJ f (b.ident INSERT idents g) UNIV` by fs[INJ_INSERT] >>
  Cases_on `b.ident = a.ident`
  >- simp[add_postactionID, idents_imap] >>
  `f a.ident ≠ f b.ident` by fs[INJ_IFF] >>
  fs[imap_add_action, add_action_add_postaction_ASSOC, INSERT_COMM]);

(* ----------------------------------------------------------------------
    folding add_action
   ---------------------------------------------------------------------- *)

val IN_FOLD_add_action = store_thm(
  "IN_FOLD_add_action",
  ``ALL_DISTINCT l ∧ (∀x y. (f x).ident = (f y).ident ⇔ x = y) ⇒
    ∀a. a ∈ FOLDR (add_action o f) emptyG l ⇔ ∃i. MEM i l ∧ a = f i``,
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  simp[idents_thm] >> metis_tac[]);

(* the ALL_DISTINCT assumption is reasonable given our setting *)
val FOLD_add_action_edges_ALL_DISTINCT = store_thm(
  "FOLD_add_action_edges_ALL_DISTINCT",
  ``ALL_DISTINCT l ∧ (∀x y. (f x).ident = (f y).ident ⇔ x = y) ⇒
    (a1 -<FOLDR (add_action o f) emptyG l>-> a2 ⇔
     ∃i j. i < j ∧ j < LENGTH l ∧ a1 = f (EL i l) ∧ a2 = f (EL j l) ∧
           touches a1 a2)``,
  Induct_on `l` >> simp[IN_FOLD_add_action, add_action_edges] >>
  simp[idents_thm] >> qx_gen_tac `h` >> strip_tac >>
  fs[] >> qpat_assum `XX a1 a2 ⇔ YY` kall_tac >> eq_tac >> strip_tac >| [
    qmatch_assum_rename_tac `MEM i l` >>
    `∃n. n < LENGTH l ∧ i = EL n l` by metis_tac[MEM_EL] >>
    map_every qexists_tac [`0`, `SUC n`] >> simp[],
    qmatch_assum_rename_tac `a1 = f (EL i l)` >>
    qmatch_assum_rename_tac `a2 = f (EL j l)` >>
    map_every qexists_tac [`SUC i`, `SUC j`] >> simp[],
    qmatch_assum_rename_tac `a1 = f (EL i (h::l))` >>
    qmatch_assum_rename_tac `a2 = f (EL j (h::l))` >>
    `i = 0 ∨ ∃i0. i = SUC i0` by (Cases_on `i` >> simp[])
    >- (disj1_tac >> fs[] >>
        `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >>
        fs[] >> simp[IN_FOLD_add_action] >> metis_tac[MEM_EL]) >>
    disj2_tac >>
    `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
    metis_tac[]
  ]);

val FOLDR_add_action_nodes = store_thm(
  "FOLDR_add_action_nodes",
  ``ALL_DISTINCT (MAP action_ident l) ∧
    DISJOINT (IMAGE action_ident (set l)) (idents G) ⇒
    ag_nodes (FOLDR add_action G l) = ag_nodes G ∪ set l``,
  simp[EXTENSION] >> Induct_on `l` >> simp[idents_thm] >>
  metis_tac[MEM_MAP]);

val INJ_COMPOSE_IMAGE = store_thm(
  "INJ_COMPOSE_IMAGE",
  ``INJ (f o g) s t ==> INJ f (IMAGE g s) t``,
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [INJ_IFF] THEN METIS_TAC[]);

val FOLDR_add_iterupd = store_thm(
  "FOLDR_add_iterupd",
  ``INJ g (idents (FOLDR (add_action o f) emptyG l)) UNIV ⇒
    FOLDR (add_action o (λa. a with ident updated_by g) o f) emptyG l =
    imap g (FOLDR (add_action o f) emptyG l)``,
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  simp[imap_add_action] >>
  imp_res_tac (INJ_INSERT |> SPEC_ALL |> EQ_IMP_RULE |> #1
                          |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
                          |> GEN_ALL) >>
  fs[]);

(* ----------------------------------------------------------------------
    Generic graph "evaluation"
   ---------------------------------------------------------------------- *)

val (genEvalG_rules, genEvalG_ind, genEvalG_cases) = Hol_reln`
  (∀s. genEvalG ap s emptyG s) ∧
  (∀s0 g a s.
     a ∈ g ∧ (∀a'. a' ∈ g ⇒ a' -<g>/-> a) ∧
     genEvalG ap (ap a s0) (g \\ a) s  ⇒
     genEvalG ap s0 g s)
`
val genEvalG_empty = store_thm(
  "genEvalG_empty[simp]",
  ``genEvalG ap s1 emptyG s2 ⇔ (s1 = s2)``,
  simp[Once genEvalG_cases] >> metis_tac[]);

val genEvalG_total = store_thm(
  "genEvalG_total",
  ``∀g s0. ∃s. genEvalG ap s0 g s``,
  gen_tac >> Induct_on `gCARD g` >> simp[] >>
  rpt strip_tac >> `ag_nodes g ≠ ∅` by (strip_tac >> fs[]) >>
  `∃a. a ∈ g ∧ ∀a'. a' ∈ g ⇒ a' -<g>/-> a`
    by metis_tac[nonempty_wfG_has_points] >>
  `gCARD (g \\ a) = v` by simp[] >>
  metis_tac[genEvalG_rules]);

val genEvalG_det = store_thm(
  "genEvalG_det",
  ``(∀a1 a2 s. ¬touches a1 a2 ∧ a1.ident ≠ a2.ident ⇒
               ap a2 (ap a1 s) = ap a1 (ap a2 s)) ⇒
    ∀s0 g s1 s2. genEvalG ap s0 g s1 ∧ genEvalG ap s0 g s2 ⇒ s1 = s2``,
  strip_tac >> rpt gen_tac >> map_every qid_spec_tac [`s0`, `s1`, `s2`] >>
  completeInduct_on `gCARD g` >> qx_gen_tac `g` >>
  qmatch_rename_tac `n = gCARD g ⇒ _` >> strip_tac >>
  map_every qx_gen_tac [`s2`, `s1`, `s0`] >> strip_tac >>
  Cases_on `g = emptyG`
  >- (RULE_ASSUM_TAC (ONCE_REWRITE_RULE [genEvalG_cases]) >> fs[]) >>
  `0 < gCARD g`
    by (simp[] >> spose_not_then assume_tac >> fs[]) >>
  Q.UNDISCH_THEN `genEvalG ap s0 g s1` mp_tac >>
  simp[Once genEvalG_cases] >>
  disch_then (qx_choose_then `a1` strip_assume_tac) >>
  Q.UNDISCH_THEN `genEvalG ap s0 g s2` mp_tac >>
  simp[Once genEvalG_cases] >>
  disch_then (qx_choose_then `a2` strip_assume_tac) >>
  Cases_on `a1 = a2`
  >- (`gCARD (g \\ a2) < n` by simp[] >> metis_tac[]) >>
  `¬touches a1 a2` by metis_tac[touching_actions_link] >>
  `a1.ident ≠ a2.ident` by metis_tac[ident_11] >>
  `a2 ∈ g \\ a1 ∧ a1 ∈ g \\ a2` by simp[] >>
  `g \\ a2 \\ a1 = g \\ a1 \\ a2`
    by (simp[graph_equality] >> metis_tac[]) >>
  `∀a'. a' ∈ g \\ a2 ⇒ a' -<g \\ a2>/-> a1` by simp[] >>
  `∀a'. a' ∈ g \\ a1 ⇒ a' -<g \\ a1>/-> a2` by simp[] >>
  `∃s. genEvalG ap (ap a1 (ap a2 s0)) (g \\ a2 \\ a1) s`
     by metis_tac[genEvalG_total] >>
  `ap a1 (ap a2 s0) = ap a2 (ap a1 s0)` by metis_tac[] >>
  `gCARD (g \\ a1) < n ∧ gCARD (g \\ a2) < n` by simp[] >>
  metis_tac[genEvalG_rules])

val genEvalG_imap_irrelevance = store_thm(
  "genEvalG_imap_irrelevance",
  ``(∀a f s. ap (a with ident updated_by f) s = ap a s) ⇒
    ∀s0 G s. genEvalG ap s0 G s ⇒ genEvalG ap s0 (imap f G) s``,
  strip_tac >> map_every qx_gen_tac [`s0`, `G`, `s`] >>
  reverse (Cases_on `INJ f (idents G) UNIV`)
  >- simp[imap_id] >>
  pop_assum (fn inj => disch_then (fn g => mp_tac inj >> mp_tac g)) >>
  map_every qid_spec_tac [`s`, `G`, `s0`] >>
  Induct_on `genEvalG` >> rpt strip_tac >> simp[] >>
  match_mp_tac (genEvalG_rules |> SPEC_ALL |> CONJUNCT2) >>
  dsimp[imap_edges] >>
  qexists_tac `a` >> simp[] >>
  `∀a1 a2. a1 ∈ G ∧ a2 ∈ G ⇒
           (a1 with ident updated_by f = a2 with ident updated_by f ⇔
            a1 = a2)`
    by (rpt strip_tac >> fds[INJ_IFF, idents_thm] >> simp[EQ_IMP_THM] >>
        simp[action_component_equality]) >>
  reverse conj_tac
  >- (`INJ f (idents (G \\ a)) UNIV` by fds[INJ_IFF, idents_thm] >>
      `imap f G \\ (a with ident updated_by f) = imap f (G \\ a)`
         suffices_by simp[] >>
      dsimp[graph_equality, imap_edges, EQ_IMP_THM, IN_imap] >> csimp[] >>
      rpt strip_tac
      >- (ntac 2 (pop_assum mp_tac) >> imp_res_tac IN_edges >> simp[] >>
          metis_tac[]) >>
      metis_tac[IN_edges]) >>
  rpt gen_tac >>
  qmatch_rename_tac `a0 ∈ G ⇒ a1' -<G>/-> a2' ∨ _` >> strip_tac >>
  Cases_on `a1' -<G>-> a2'` >> simp[] >> metis_tac[IN_edges]);

(* ----------------------------------------------------------------------
    Define a gEVAL constant to be the function of the relation
   ---------------------------------------------------------------------- *)

val gEVAL_def = new_specification(
  "gEVAL_def", ["gEVAL"],
  genEvalG_total |> SPEC_ALL |> Q.GENL [`g`, `s0`, `ap`]
                 |> SIMP_RULE bool_ss[SKOLEM_THM]);

val gEVAL_empty = store_thm(
  "gEVAL_empty[simp]",
  ``gEVAL f x emptyG = x``,
  Q.ISPEC_THEN `f` (qspecl_then [`x`, `emptyG`] assume_tac) gEVAL_def >>
  fs[]);

val gEVAL_thm = store_thm(
  "gEVAL_thm",
  ``(∀a1 a2 s. ¬touches a1 a2 ∧ a1.ident ≠ a2.ident ⇒
               ap a2 (ap a1 s) = ap a1 (ap a2 s)) ⇒
    (∀s0. gEVAL ap s0 emptyG = s0) ∧
    (∀a s0. a.ident ∉ idents g ⇒
            gEVAL ap s0 (a ⊕ g) = gEVAL ap (ap a s0) g)``,
  rpt strip_tac >> simp[] >>
  `a ∈ a ⊕ g` by simp[] >>
  `a ∉ g` by (strip_tac >> fs[idents_thm]) >>
  `∀a'. a' ∈ a ⊕ g ⇒ a' -<a ⊕ g>/-> a`
     by (dsimp[add_action_edges] >> metis_tac[IN_edges]) >>
  `genEvalG ap (ap a s0) g (gEVAL ap (ap a s0) g)` by metis_tac[gEVAL_def] >>
  `(a ⊕ g) \\ a = g`
    by (csimp[graph_equality, add_action_edges] >> metis_tac[IN_edges]) >>
  `genEvalG ap s0 (a ⊕ g) (gEVAL ap (ap a s0) g)`
    by metis_tac[genEvalG_rules] >>
  metis_tac[genEvalG_det, gEVAL_def]);

val gEVAL_imap_irrelevance = store_thm(
  "gEVAL_imap_irrelevance",
  ``(∀a f s. ap (a with ident updated_by f) s = ap a s) ∧
    (∀a1 a2 s. ¬(a1 ∼ₜ a2) ∧ a1.ident ≠ a2.ident ⇒
               ap a2 (ap a1 s) = ap a1 (ap a2 s)) ⇒
    ∀s0 f G. gEVAL ap s0 (imap f G) = gEVAL ap s0 G``,
  rpt strip_tac >>
  `genEvalG ap s0 G (gEVAL ap s0 G)` by metis_tac[gEVAL_def] >>
  `genEvalG ap s0 (imap f G) (gEVAL ap s0 G)`
    by metis_tac[genEvalG_imap_irrelevance] >>
  `genEvalG ap s0 (imap f G) (gEVAL ap s0 (imap f G))`
    by metis_tac [gEVAL_def] >> metis_tac[genEvalG_det]);

(* ----------------------------------------------------------------------
    Merging graphs, second graph is added to the "back" of the first.
   ---------------------------------------------------------------------- *)

val add_postaction_commutes = store_thm(
  "add_postaction_commutes",
  ``∀a1 a2 g. ¬touches a1 a2 ∧ a1.ident ≠ a2.ident ⇒
              add_postaction a2 (add_postaction a1 g) =
              add_postaction a1 (add_postaction a2 g)``,
  rpt strip_tac >>
  simp[graph_equality, add_postaction_edges] >> conj_tac
  >- dsimp[EQ_IMP_THM] >>
  simp[EQ_IMP_THM] >> rw[] >> fs[] >> metis_tac[touches_SYM])

val merge_graph_def = Define`merge_graph = gEVAL add_postaction`;

val merge_graph_thm = save_thm(
  "merge_graph_thm",
  MATCH_MP gEVAL_thm add_postaction_commutes
           |> REWRITE_RULE [GSYM merge_graph_def])

val IN_merge_graph = store_thm(
  "IN_merge_graph[simp]",
  ``a ∈ merge_graph g1 g2 ⇔
     a ∈ g1 ∨ a.ident ∉ idents g1 ∧ a ∈ g2``,
  map_every qid_spec_tac [`a`, `g1`, `g2`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm] >> rpt gen_tac >> strip_tac >>
  dsimp[EQ_IMP_THM] >> rpt strip_tac >>
  qmatch_assum_rename_tac `b.ident ∉ idents g1` >>
  Cases_on `a.ident = b.ident` >> fs[idents_thm]);

val idents_merge_graph = store_thm(
  "idents_merge_graph[simp]",
  ``idents (merge_graph g1 g2) = idents g1 ∪ idents g2``,
  dsimp[idents_thm, EXTENSION] >> metis_tac[ident_11]);

val merge_graph_postaction_ASSOC = store_thm(
  "merge_graph_postaction_ASSOC",
  ``merge_graph g1 (add_postaction a g2) =
    add_postaction a (merge_graph g1 g2)``,
  Cases_on `a.ident ∈ idents g2`
  >- (`add_postaction a g2 = g2`
        by simp[graph_equality, add_postaction_edges] >>
      `add_postaction a (merge_graph g1 g2) = merge_graph g1 g2`
        by simp[graph_equality, add_postaction_edges] >>
      simp[]) >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`a`, `g1`, `g2`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm] >> map_every qx_gen_tac [`a`, `g2`] >> strip_tac >>
  map_every qx_gen_tac [`g1`, `b`] >> strip_tac >>
  simp[add_action_add_postaction_ASSOC, merge_graph_thm]);

val merge_graph_addaction_ASSOC = store_thm(
  "merge_graph_addaction_ASSOC",
  ``a.ident ∉ idents g2 ⇒ merge_graph (a ⊕ g1) g2 = a ⊕ merge_graph g1 g2``,
  map_every qid_spec_tac [`a`, `g1`, `g2`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm, add_action_add_postaction_ASSOC]);

val merge_graph_ASSOC = store_thm(
  "merge_graph_ASSOC",
  ``merge_graph g1 (merge_graph g2 g3) = merge_graph (merge_graph g1 g2) g3``,
  map_every qid_spec_tac [`g1`, `g2`, `g3`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm, merge_graph_postaction_ASSOC]);

val merge_graph_emptyL = store_thm(
  "merge_graph_emptyL",
  ``∀g. merge_graph emptyG g = g``,
  ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm, merge_graph_addaction_ASSOC]);

val merge_graph_empty = store_thm(
  "merge_graph_empty[simp]",
  ``merge_graph emptyG g = g ∧ merge_graph g emptyG = g``,
  simp[merge_graph_thm, merge_graph_emptyL]);

val nontouching_merge_COMM = store_thm(
  "nontouching_merge_COMM",
  ``∀g1 g2. ¬gtouches g1 g2 ∧ DISJOINT (idents g1) (idents g2) ⇒
            merge_graph g1 g2 = merge_graph g2 g1``,
  ho_match_mp_tac graph_ind >> simp[merge_graph_thm] >> rpt strip_tac >>
  `add_postaction a g2 = a ⊕ g2` by metis_tac[add_postaction_EQ_add_action] >>
  simp[merge_graph_addaction_ASSOC] >> metis_tac[]);

val gtouches_imap = store_thm(
  "gtouches_imap[simp]",
  ``(gtouches (imap f g1) g2 ⇔ gtouches g1 g2) ∧
    (gtouches g1 (imap f g2) ⇔ gtouches g1 g2)``,
  simp[gtouches_def] >> conj_tac
  >- (Cases_on `INJ f (idents g1) UNIV` >>
      simp[IN_imap, PULL_EXISTS, imap_id] >> metis_tac[])
  >- (Cases_on `INJ f (idents g2) UNIV` >>
      simp[IN_imap, PULL_EXISTS, imap_id] >> metis_tac[]))

(* ----------------------------------------------------------------------
    pregraph : action -> graph -> graph

    [pregraph a g] returns the sub-graph of g that strictly precedes
    action a.  If a is not in the graph, returns the empty graph.

   ---------------------------------------------------------------------- *)

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
  ``a.ident ∉ idents g ⇒ pregraph a (a ⊕ g) = emptyG``,
  dsimp[pregraph_def, add_action_edges] >> csimp[] >> strip_tac >>
  `a ∉ g` by (strip_tac >> fs[idents_thm]) >>
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
  ``∀s. FINITE s ⇒ ∀g a. a ∉ s ∧ a.ident ∉ idents g ⇒
        ITSET (λb g. g \\ b) s (a ⊕ g) = a ⊕ ITSET (λb g. g \\ b) s g``,
  Induct_on `FINITE s` >>
  simp[ITSET_EMPTY, COMMUTING_ITSET_INSERT, gDELETE_commutes,
       DELETE_NON_ELEMENT_RWT] >>
  rpt strip_tac >>
  `a.ident ∉ idents (g \\ e)` by (fs[idents_thm] >> metis_tac[]) >>
  `(a ⊕ g) \\ e = a ⊕ (g \\ e)` suffices_by simp[] >>
  simp[graph_equality, add_action_edges, EQ_IMP_THM] >> rpt strip_tac >>
  simp[] >> metis_tac[]);

val pregraph_add_action_1 = prove(
  ``a.ident ∉ idents g ∧ a ≠ b ∧ b ∈ g ∧ a ∼ₜ b ⇒
    pregraph b (a ⊕ g) = a ⊕ pregraph b g``,
  simp[pregraph_def, add_action_edges] >> dsimp[] >> csimp[] >>
  strip_tac >>
  qmatch_abbrev_tac `ITSET del s1 (a ⊕ g) = a ⊕ ITSET del s2 g` >>
  `a ∉ g` by (strip_tac >> fs[idents_thm]) >>
  `s1 = s2`
    by dsimp[EXTENSION, Abbr`s1`, Abbr`s2`, EQ_IMP_THM] >>
  simp[Abbr`del`] >> `FINITE s2 ∧ a ∉ s2` suffices_by metis_tac[ITSET_DEL] >>
  rpt strip_tac
  >- (match_mp_tac SUBSET_FINITE_I >> qexists_tac `ag_nodes g` >>
      simp[SUBSET_DEF, Abbr`s2`]) >>
  qunabbrev_tac `s2` >> fs[]);

val pregraph_add_action_2 = prove(
  ``a.ident ∉ idents g ∧ a ≠ b ∧ b ∈ g ∧ a ≁ₜ b ⇒
    pregraph b (a ⊕ g) = pregraph b g``,
  simp[pregraph_def, add_action_edges] >> rpt strip_tac >>
  `a ∉ g` by (strip_tac >> fs[idents_thm]) >>
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
  ``a.ident ∉ idents g ⇒
    pregraph b (a ⊕ g) =
      if b ∈ g then
        (if a ∼ₜ b then add_action a else I)
        (pregraph b g)
      else emptyG``,
  strip_tac >> `a ∉ g` by (strip_tac >> fs[idents_thm]) >>
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
      Cases_on `a.ident = b.ident` >- simp[add_postactionID] >>
      simp[add_action_add_postaction_ASSOC]) >>
  map_every qx_gen_tac [`a`, `g`, `c`] >> rpt strip_tac >>
  Cases_on `a.ident = b.ident` >- simp[add_postactionID] >>
  simp[add_action_add_postaction_ASSOC, pregraph_add_action]);

val pregraph_merge_graph = store_thm(
  "pregraph_merge_graph",
  ``∀g2 g1 a. a ∈ g1 ⇒ pregraph a (merge_graph g1 g2) = pregraph a g1``,
  ho_match_mp_tac graph_ind >> dsimp[merge_graph_thm, pregraph_add_postaction]);

val IN_FOLDRi_merge_graph = store_thm(
  "IN_FOLDRi_merge_graph",
  ``(∀i. i < LENGTH list ⇒
         DISJOINT (idents (f i (EL i list))) (idents acc)) ∧
    (∀i j. i < j ∧ j < LENGTH list ⇒
           DISJOINT (idents (f i (EL i list)))
                    (idents (f j (EL j list)))) ⇒
    (a ∈ FOLDRi (λn c. merge_graph (f n c)) acc list ⇔
     a ∈ acc ∨ ∃i. i < LENGTH list ∧ a ∈ f i (EL i list))``,
  qid_spec_tac `f` >>
  Induct_on `list` >> dsimp[combinTheory.o_ABS_L, LT_SUC] >>
  rw[EQ_IMP_THM] >> simp[]
  >- metis_tac[]
  >- (`a.ident ∈ idents acc` by simp[idents_thm] >>
      fs[DISJOINT_DEF, EXTENSION] >> metis_tac[])
  >- (`a.ident ∉ idents (f 0 h)` suffices_by metis_tac[] >>
      `a.ident ∈ idents (f (SUC n0) (EL n0 list))` by simp[idents_thm] >>
      fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]))

val IN_FOLDRi_merge_graph' =
    IN_FOLDRi_merge_graph |> Q.INST [`acc` |-> `emptyG`]
                          |> SIMP_RULE (srw_ss()) []

val idents_FOLDRi_merge = store_thm(
  "idents_FOLDRi_merge",
  ``∀g.
      idents (FOLDRi (λn c. merge_graph (g n c)) a l) =
        BIGUNION (IMAGE (λi. idents (g i (EL i l))) (count (LENGTH l))) ∪
        idents a``,
  Induct_on `l` >> simp[combinTheory.o_ABS_L] >>
  dsimp[Once EXTENSION, LT_SUC] >> metis_tac[]);

val pregraph_FOLDRi_merge_graph = store_thm(
  "pregraph_FOLDRi_merge_graph",
  ``∀list n f.
      n < LENGTH list ∧ a ∈ f n (EL n list) ∧
      (∀i j. i < j ∧ j < LENGTH list ⇒
             ¬gtouches (f i (EL i list)) (f j (EL j list)) ∧
             DISJOINT (idents (f i (EL i list)))
                      (idents (f j (EL j list)))) ⇒
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
  dsimp[idents_FOLDRi_merge, Abbr`g2`] >>
  simp[gtouches_def, IN_FOLDRi_merge_graph] >>
  metis_tac[gtouches_def]);

val _ = type_abbrev("G", ``:('a,'b,'c) action_graph``)

val dgSIGMA_def = Define`
  dgSIGMA f g = gEVAL (λa tot. tot + f a.data) 0 g
`

val add_t = ``λa tot. tot + f a.data``

val lemma = gEVAL_thm
              |> Q.GEN `ap`
              |> ISPEC add_t
              |> SIMP_RULE (srw_ss() ++ ARITH_ss) []
              |> CONJUNCTS

val add_folds_right = prove(
  ``∀g a acc.
      a.ident ∉ idents g ⇒
      gEVAL ^add_t acc (a ⊕ g) = ^add_t a (gEVAL ^add_t acc g)``,
  ho_match_mp_tac graph_ind >> simp lemma);

val dgSIGMA_thm = store_thm(
  "dgSIGMA_thm[simp]",
  ``dgSIGMA f (emptyG : (α,β,γ)G) = 0 ∧
    (a.ident ∉ idents (g:(α,β,γ)G) ⇒ dgSIGMA f (a ⊕ g) = f a.data + dgSIGMA f g)``,
  simp[add_folds_right, dgSIGMA_def] >> simp[gEVAL_thm]);

val dgSIGMA_CONG = store_thm(
  "dgSIGMA_CONG",
  ``∀f1 f2 g1 g2.
      (∀d. d ∈ IMAGE action_data (ag_nodes g1) ⇒ f1 d = f2 d) ∧
      g1 = g2 ⇒ dgSIGMA f1 g1 = dgSIGMA f2 g2``,
  simp[PULL_EXISTS] >> map_every qx_gen_tac [`f1`, `f2`] >>
  ho_match_mp_tac graph_ind >> simp[]);

val dgSIGMA_dgmap = store_thm(
  "dgSIGMA_dgmap[simp]",
  ``∀G. dgSIGMA f (dgmap g G) = dgSIGMA (f o g) G``,
  ho_match_mp_tac graph_ind >> simp[polydata_upd_def]);

val _ = export_theory();
