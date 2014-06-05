open HolKernel Parse boolLib bossLib;

open primitivesTheory pred_setTheory listRangeTheory listTheory
open finite_mapTheory
open lcsymtacs

val _ = new_theory "actionGraph";

val _ = Hol_datatype`
  action = <|
    write : 'access ;
    reads : 'access list ;
    expr : 'a list -> 'a;
    iter : 'iter
  |>
`;

val action_component_equality = theorem "action_component_equality"

val touches_def = Define`
  touches a1 a2 ⇔
     a1.write = a2.write ∨ MEM a1.write a2.reads ∨ MEM a2.write a1.reads
`;

val _ = set_mapped_fixity {term_name = "touches", fixity = Infix(NONASSOC, 450),
                           tok = "∼ₜ"}

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

val touches_REFL = store_thm(
  "touches_REFL",
  ``touches a a``,
  simp[touches_def]);
val _ = export_rewrites ["touches_REFL"]

val touches_SYM = store_thm(
  "touches_SYM",
  ``touches a1 a2 ⇒ touches a2 a1``,
  simp[touches_def] >> rpt strip_tac >> simp[]);

val _ = Hol_datatype`
  action_graph0 = <|
    nodes : ('a,'acc,'iter) action set;
    edges : ('a,'acc,'iter) action -> ('a,'acc,'iter) action set
  |>
`

val wfG_def = Define`
  wfG G ⇔
      FINITE G.nodes ∧
      (∀a1 a2. G.edges a1 a2 ⇒ touches a1 a2 ∧ a1 ∈ G.nodes ∧ a2 ∈ G.nodes) ∧
      (∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ touches a1 a2 ∧ a1 ≠ a2 ⇒ (¬G.edges a1 a2 ⇔ G.edges a2 a1)) ∧
      (∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ G.edges⁺ a1 a2 ⇒ ¬G.edges⁺ a2 a1) ∧
      INJ (λa. a.iter) G.nodes univ(:'iter)
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

val iterations0_def = Define`
  iterations0 G = IMAGE (\a. a.iter) G.nodes
`;

val add_action0_def = Define`
  add_action0 a G =
    if a.iter ∈ iterations0 G then G
    else
      <| nodes := a INSERT G.nodes ;
         edges := (λsrc tgt. G.edges src tgt ∨
                             src = a ∧ touches a tgt ∧ tgt ∈ G.nodes) |>
`;

val add_postaction0_def = Define`
  add_postaction0 a G =
    if a.iter ∈ iterations0 G then G
    else
      <| nodes := a INSERT G.nodes ;
         edges := (λsrc tgt. G.edges src tgt ∨
                             src ∈ G.nodes ∧ touches src tgt ∧ tgt = a) |>
`;

val _ = IndDefLib.export_rule_induction "relation.TC_STRONG_INDUCT"
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

val INJ_THM = store_thm(
  "INJ_THM",
  ``INJ f s t ⇔
      (∀x. x ∈ s ⇒ f x ∈ t) ∧
      ∀x y. x ∈ s ∧ y ∈ s ⇒ (f x = f y ⇔ x = y)``,
  metis_tac[INJ_DEF]);

val wfG_add_action0 = prove(
  ``wfG G ⇒ wfG (add_action0 a G)``,
  rw[add_action0_def] >>
  qabbrev_tac `
    R' = (λsrc tgt. G.edges src tgt ∨ src = a ∧ touches a tgt ∧ tgt ∈ G.nodes)
  ` >>
  `∀x y. G.edges x y ∨ x = a ∧ touches a y ∧ y ∈ G.nodes <=> R' x y`
    by simp[Abbr`R'`] >>
  markerLib.RM_ALL_ABBREVS_TAC >> fs[wfG_def, iterations0_def] >> reverse (rpt strip_tac)
  >- (fs[INJ_THM] >> metis_tac[])
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
  fs[wfG_def, iterations0_def] >> reverse (rpt strip_tac)
  >- (fs[INJ_THM] >> metis_tac[])
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
    a.iter ∉ iterations0 G ∧ x = a ∨ x ∈ G.nodes``,
  rw[add_action0_def]);

val IN_add_postaction0 = prove(
  ``x ∈ (add_postaction0 a G).nodes <=>
    a.iter ∉ iterations0 G ∧ x = a ∨ x ∈ G.nodes``,
  rw[add_postaction0_def]);

val add_action0_edges = prove(
  ``(add_action0 a G).edges a1 a2 ⇔
      a.iter ∉ iterations0 G ∧ a1 = a ∧ a2 ∈ G.nodes ∧ touches a1 a2 ∨
      G.edges a1 a2``,
  rw[add_action0_def] >> metis_tac[]);

val add_postaction0_edges = prove(
  ``(add_postaction0 a G).edges a1 a2 <=>
       a.iter ∉ iterations0 G ∧ a1 ∈ G.nodes ∧ a2 = a ∧ touches a1 a2 ∨
       G.edges a1 a2``,
  rw[add_postaction0_def] >> metis_tac[]);

val fmap0_def = Define`
  fmap0 G = FUN_FMAP (λi. @a. a ∈ G.nodes ∧ a.iter = i) (iterations0 G)
`;

val FDOM_fmap0 = prove(
  ``!g::respects wfEQ. FDOM (fmap0 g) = iterations0 g``,
  simp[fmap0_def, FUN_FMAP_DEF, wfEQ_def, wfG_FINITE, iterations0_def,
       IMAGE_FINITE, quotientTheory.respects_def, INWR]);

val fmap0_add_action0 = prove(
  ``!g::respects wfEQ.
       fmap0 (add_action0 a g) ' i = if a.iter = i ∧ i ∉ iterations0 g then a
                                     else fmap0 g ' i``,
  simp[wfEQ_def, quotientTheory.respects_def, INWR, RES_FORALL_THM] >>
  rw[add_action0_def] >> fs[wfG_def, INJ_THM, fmap0_def, iterations0_def] >| [
    metis_tac[],
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    `∀b. b ∈ g.nodes ∧ b.iter = a.iter <=> F`
      suffices_by disch_then (fn th => simp[th]) >>
    metis_tac[],
    Cases_on `i ∈ IMAGE (λa. a.iter) g.nodes`
    >- (dsimp[IMAGE_FINITE, FUN_FMAP_DEF] >> csimp[]) >>
    simp[IMAGE_FINITE, NOT_FDOM_FAPPLY_FEMPTY, FUN_FMAP_DEF],
    `a.iter ≠ a'.iter` by metis_tac[] >>
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    metis_tac[]
  ]);

val fmap0_add_postaction0 = prove(
  ``!g::respects wfEQ.
       fmap0 (add_postaction0 a g) ' i =
         if a.iter = i ∧ i ∉ iterations0 g then a
         else fmap0 g ' i``,
  simp[wfEQ_def, quotientTheory.respects_def, INWR, RES_FORALL_THM] >>
  rw[add_postaction0_def] >> fs[wfG_def, INJ_THM, fmap0_def, iterations0_def] >| [
    metis_tac[],
    simp[IMAGE_FINITE, FUN_FMAP_DEF] >> dsimp[] >> csimp[] >>
    `∀b. b ∈ g.nodes ∧ b.iter = a.iter <=> F`
      suffices_by disch_then (fn th => simp[th]) >>
    metis_tac[],
    Cases_on `i ∈ IMAGE (λa. a.iter) g.nodes`
    >- (dsimp[IMAGE_FINITE, FUN_FMAP_DEF] >> csimp[]) >>
    simp[IMAGE_FINITE, NOT_FDOM_FAPPLY_FEMPTY, FUN_FMAP_DEF],
    `a.iter ≠ a'.iter` by metis_tac[] >>
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
  simp[gDELETE0_def, wfG_def, INJ_THM] >> reverse (rpt strip_tac)
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
  qmatch_assum_rename_tac `(RIMAGE f R)⁺ x a` [] >>
  qmatch_assum_rename_tac `(RIMAGE f R)⁺ a y` [] >>
  `∃a0. a0 ∈ field R ∧ f a0 = a` by metis_tac[RIMAGE_TC_IN_field] >>
  metis_tac[relationTheory.TC_RULES]);


val imap0_def = Define`
  imap0 f G = if INJ f (iterations0 G) UNIV then
                G with <| nodes updated_by IMAGE (λa. a with iter updated_by f);
                          edges updated_by RIMAGE (λa. a with iter updated_by f)
                       |>
              else G
`;

val imap0_id = prove(
  ``¬INJ f (iterations0 G) UNIV ⇒ imap0 f G = G``,
  simp[imap0_def]);

val wfG_imap = prove(
  ``wfG G ⇒ wfG (imap0 f G)``,
  simp[imap0_def, iterations0_def] >> COND_CASES_TAC >> simp[] >>
  simp[wfG_def, RIMAGE_DEF] >> strip_tac >>
  qabbrev_tac `f' = λa. a with iter updated_by f` >> simp[] >>
  `∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ⇒ (f' a1 = f' a2 ⇔ a1 = a2)`
    by (rpt strip_tac >> simp[action_component_equality, Abbr`f'`] >>
        full_simp_tac (srw_ss() ++ boolSimps.DNF_ss) [INJ_THM]) >>
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
  full_simp_tac (srw_ss() ++ boolSimps.DNF_ss)[INJ_THM, Abbr`f'`])

val wfEQ_imap0 = prove(
  ``wfEQ g1 g2 ⇒ wfEQ (imap0 f g1) (imap0 f g2)``,
  csimp[wfEQ_def, wfG_imap]);

val imap_emptyG0 = prove(
  ``imap0 f emptyG0 = emptyG0``,
  simp[emptyG0_def, imap0_def]);

val IN_imap0 = prove(
  ``INJ f (iterations0 G) UNIV ⇒ (a ∈ (imap0 f G).nodes ⇔ ∃a0. a0 ∈ G.nodes ∧ a = a0 with iter updated_by f)``,
  simp[imap0_def] >> metis_tac[]);

val imap0_edges = prove(
  ``INJ f (iterations0 G) UNIV ⇒
    ((imap0 f G).edges a1 a2 ⇔
      ∃a10 a20. G.edges a10 a20 ∧ a1 = a10 with iter updated_by f ∧
                a2 = a20 with iter updated_by f)``,
  simp[imap0_def, RIMAGE_DEF] >> metis_tac[]);

val iter0_11 = prove(
  ``∀g. wfG g ⇒ INJ (λa. a.iter) g.nodes UNIV``,
  simp[wfG_def]);

val frange_fmap0 = prove(
  ``∀g. wfG g ⇒ FRANGE (fmap0 g) = g.nodes``,
  simp[fmap0_def, FRANGE_FMAP, iterations0_def, IMAGE_FINITE, wfG_FINITE,
       GSYM IMAGE_COMPOSE, combinTheory.o_ABS_R] >>
  simp[EXTENSION, EQ_IMP_THM] >> rw[]
  >- (SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >> simp[]) >>
  qexists_tac `x` >>
  imp_res_tac iter0_11 >> fs[INJ_THM] >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >> metis_tac[])

val fmap0_inverts_iter = prove(
  ``∀(g::respects wfEQ). ∀a. a ∈ g.nodes ⇒ fmap0 g ' a.iter = a``,
  simp[fmap0_def, iterations0_def, FUN_FMAP_DEF, IMAGE_FINITE, wfG_FINITE,
       wfEQ_def, RES_FORALL_THM, quotientTheory.IN_RESPECTS] >>
  rpt strip_tac >> SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  fs[wfG_def, INJ_THM] >> metis_tac[]);

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
     iterations_thm, FDOM_fmap,
     fmap_add_action, fmap_add_postaction,
     IN_edges,
     IN_gDELETE, nodes_gDELETE, gDELETE_edges, gDELETE_commutes,
     imap_emptyG, IN_imap, imap_edges, touching_actions_link, imap_id,
     iter_INJ, frange_fmap, fmap_inverts_iter] =
define_quotient {
  types = [{name = "action_graph", equiv = wfEQ_equiv}],
  defs = [("emptyG",``emptyG0``),
          ("iterations", ``iterations0``),
          ("ag_nodes", ``action_graph0_nodes``),
          ("ag_edges", ``action_graph0_edges``),
          ("add_action", ``add_action0``),
          ("add_postaction", ``add_postaction0``),
          ("fmap", ``fmap0``),
          ("gDELETE", ``gDELETE0``),
          ("imap", ``imap0``)],
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
          ("iterations_thm", iterations0_def),
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
          ("iter_INJ", mkwfeq (iter0_11)),
          ("frange_fmap", mkwfeq (frange_fmap0)),
          ("fmap_inverts_iter", fmap0_inverts_iter)],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfEQ_emptyG0, simple_rsp ``action_graph0_nodes``,
              simple_rsp ``action_graph0_edges``,
              simple_rsp ``fmap0``, wfEQ_delete,
              simple_rsp ``iterations0``, wfEQ_add_action0,
              wfEQ_add_postaction0,
              wfEQ_imap0]}

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
                         "gDELETE_edges", "edges_irrefl"]

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
       a.iter ∉ iterations g1 ∧ (∃b. b ∈ g2 ∧ touches a b) ∨ gtouches g1 g2) ∧
    (gtouches g1 (a ⊕ g2) ⇔
       a.iter ∉ iterations g2 ∧ (∃b. b ∈ g1 ∧ touches b a) ∨ gtouches g1 g2)``,
  simp[gtouches_def] >> metis_tac[]);

val iterations_add_action = store_thm(
  "iterations_add_action[simp]",
  ``iterations (add_action a G) = a.iter INSERT iterations G``,
  dsimp[iterations_thm, EXTENSION, EQ_IMP_THM] >> metis_tac[]);

val iterations_add_postaction = store_thm(
  "iterations_add_postaction[simp]",
  ``iterations (add_postaction a G) = a.iter INSERT iterations G``,
  dsimp[iterations_thm, EXTENSION, EQ_IMP_THM] >> metis_tac[]);

val iterations_emptyG = store_thm(
  "iterations_emptyG[simp]",
  ``iterations emptyG = ∅``,
  simp[iterations_thm]);

val iter_11 = store_thm(
  "iter_11",
  ``a1 ∈ G ∧ a2 ∈ G ⇒ (a1.iter = a2.iter ⇔ a1 = a2)``,
  metis_tac[iter_INJ, INJ_THM]);

val add_action_EQ_emptyG = store_thm(
  "add_action_EQ_emptyG[simp]",
  ``add_action a G ≠ emptyG``,
  disch_then (mp_tac o Q.AP_TERM `iterations`) >> simp[]);

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

val ilink_def = Define`
  ilink i G j <=> i ∈ iterations G ∧ j ∈ iterations G ∧
                  fmap G ' i -<G>-> fmap G ' j
`;

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

val _ = overload_on ("'", ``\G i. fmap G ' i``)

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
     i ∈ iterations g ∧ j ∈ iterations g ⇒ (fmap g ' i = fmap g ' j ⇔ i = j)``,
  simp[EQ_IMP_THM] >> rpt strip_tac >> fs[iterations_thm] >> rw[] >>
  pop_assum mp_tac >> simp[fmap_inverts_iter]);

val BIJ_iterations_nodes = store_thm(
  "BIJ_iterations_nodes",
  ``BIJ (λa. a.iter) (ag_nodes g) (iterations g)``,
  simp[BIJ_IFF_INV] >> conj_tac >- simp[iterations_thm] >>
  qexists_tac `FAPPLY (fmap g)` >> rpt strip_tac >>
  fs[iterations_thm, fmap_inverts_iter]);

(* ----------------------------------------------------------------------
    Properties of imap
   ---------------------------------------------------------------------- *)

val iterations_imap = store_thm(
  "iterations_imap",
  ``INJ f (iterations G) UNIV ⇒
    iterations (imap f G) = IMAGE f (iterations G)``,
  dsimp[iterations_thm, EXTENSION]);

val add_action_id = store_thm(
  "add_action_id",
  ``add_action a G = G ⇔ a.iter ∈ iterations G ``,
  reverse eq_tac >- simp[graph_equality, add_action_edges] >>
  disch_then (mp_tac o Q.AP_TERM `λg. a ∈ g`) >> simp[] >>
  simp[iterations_thm] >> metis_tac[]);

val fds = full_simp_tac (srw_ss() ++ boolSimps.DNF_ss)
val imap_add_action = store_thm(
  "imap_add_action",
  ``INJ f (a.iter INSERT iterations G) UNIV ⇒
    (imap f (add_action a G) =
     add_action (a with iter updated_by f) (imap f G))``,
  strip_tac >>
  `INJ f (iterations G) UNIV` by metis_tac[INJ_INSERT] >>
  Cases_on `a.iter ∈ iterations G`
  >- (`add_action a G = G` by simp[graph_equality, add_action_edges] >>
      simp[add_action_id, iterations_imap]) >>
  simp[graph_equality, imap_edges, IN_imap, iterations_imap, imap_edges,
       add_action_edges] >> dsimp[] >> rpt strip_tac
  >- (fs[INJ_THM] >> metis_tac[]) >>
  `∀a1 a2. (a1 = a ∨ a1 ∈ G) ∧ (a2 = a ∨ a2 ∈ G) ⇒
           (a1 with iter updated_by f = a2 with iter updated_by f ⇔
            a1 = a2)`
    by (simp[EQ_IMP_THM] >> fds [INJ_THM, iterations_thm] >>
        simp[action_component_equality]) >>
  eq_tac >> rpt strip_tac
  >- (csimp[] >> disj1_tac >> spose_not_then strip_assume_tac >>
      qpat_assum `f XX = f YY` mp_tac >> fds [INJ_THM, iterations_thm] >>
      metis_tac[])
  >- metis_tac[]
  >- (csimp[] >> rw[] >> fs[]) >>
  metis_tac[]);

val INJ_COMPOSE2 = prove(
  ``INJ (f o g) s UNIV ⇒ INJ g s UNIV ∧ INJ f (IMAGE g s) UNIV``,
  dsimp[INJ_THM] >> metis_tac[]);

val imap_imap_o = store_thm(
  "imap_imap_o",
  ``INJ (f o g) (iterations G) UNIV ⇒ imap f (imap g G) = imap (f o g) G``,
  strip_tac >> imp_res_tac INJ_COMPOSE2 >>
  dsimp[graph_equality, IN_imap, imap_edges, iterations_imap]);

val iter_noop = prove(
  ``a with iter updated_by (λn. n) = a``,
  simp[action_component_equality]);

val INJ_ID_UNIV = prove(
  ``INJ (\x. x) s UNIV``,
  simp[INJ_THM]);

val imap_ID = store_thm(
  "imap_ID[simp]",
  ``imap (λn. n) G = G``,
  dsimp[graph_equality, imap_edges, INJ_ID_UNIV, iter_noop]);

val imap_CONG = store_thm(
  "imap_CONG",
  ``G = G' ⇒ (∀a. a ∈ iterations G' ⇒ f a = f' a) ⇒ imap f G = imap f' G``,
  rpt strip_tac >> Cases_on `INJ f (iterations G) UNIV`
  >- (`∀a. a ∈ G ⇒ a with iter updated_by f = a with iter updated_by f'`
        by (fds[iterations_thm] >> rpt strip_tac >>
            simp[action_component_equality]) >>
      `INJ f' (iterations G) UNIV` by (fs[INJ_THM] >> metis_tac[]) >>
      dsimp[graph_equality, imap_edges] >> csimp[] >> rpt strip_tac >>
      eq_tac >> rpt strip_tac >> csimp[] >> metis_tac[IN_edges]) >>
  `¬INJ f' (iterations G) UNIV` by (fs[INJ_THM] >> metis_tac[]) >>
  simp[imap_id]);

(* ----------------------------------------------------------------------
    folding add_action
   ---------------------------------------------------------------------- *)

val IN_FOLD_add_action = store_thm(
  "IN_FOLD_add_action",
  ``ALL_DISTINCT l ∧ (∀x y. (f x).iter = (f y).iter ⇔ x = y) ⇒
    ∀a. a ∈ FOLDR (add_action o f) emptyG l ⇔ ∃i. MEM i l ∧ a = f i``,
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  simp[iterations_thm] >> metis_tac[]);

(* the ALL_DISTINCT assumption is reasonable given our setting *)
val FOLD_add_action_edges_ALL_DISTINCT = store_thm(
  "FOLD_add_action_edges_ALL_DISTINCT",
  ``ALL_DISTINCT l ∧ (∀x y. (f x).iter = (f y).iter ⇔ x = y) ⇒
    (a1 -<FOLDR (add_action o f) emptyG l>-> a2 ⇔
     ∃i j. i < j ∧ j < LENGTH l ∧ a1 = f (EL i l) ∧ a2 = f (EL j l) ∧
           touches a1 a2)``,
  Induct_on `l` >> simp[IN_FOLD_add_action, add_action_edges] >>
  simp[iterations_thm] >> qx_gen_tac `h` >> strip_tac >>
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
        fs[] >> simp[IN_FOLD_add_action] >> metis_tac[MEM_EL]) >>
    disj2_tac >>
    `∃j0. j = SUC j0` by (Cases_on `j` >> fs[]) >> fs[] >>
    metis_tac[]
  ]);

val FOLDR_add_action_nodes = store_thm(
  "FOLDR_add_action_nodes",
  ``ALL_DISTINCT (MAP action_iter l) ∧
    DISJOINT (IMAGE action_iter (set l)) (iterations G) ⇒
    ag_nodes (FOLDR add_action G l) = ag_nodes G ∪ set l``,
  simp[EXTENSION] >> Induct_on `l` >> simp[iterations_thm] >>
  metis_tac[MEM_MAP]);

val INJ_COMPOSE_IMAGE = store_thm(
  "INJ_COMPOSE_IMAGE",
  ``INJ (f o g) s t ==> INJ f (IMAGE g s) t``,
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [INJ_THM] THEN METIS_TAC[]);

val FOLDR_add_iterupd = store_thm(
  "FOLDR_add_iterupd",
  ``INJ g (iterations (FOLDR (add_action o f) emptyG l)) UNIV ⇒
    FOLDR (add_action o (λa. a with iter updated_by g) o f) emptyG l =
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
  ``(∀a1 a2 s. ¬touches a1 a2 ∧ a1.iter ≠ a2.iter ⇒
               ap a2 (ap a1 s) = ap a1 (ap a2 s)) ⇒
    ∀s0 g s1 s2. genEvalG ap s0 g s1 ∧ genEvalG ap s0 g s2 ⇒ s1 = s2``,
  strip_tac >> rpt gen_tac >> map_every qid_spec_tac [`s0`, `s1`, `s2`] >>
  completeInduct_on `gCARD g` >> qx_gen_tac `g` >>
  qmatch_rename_tac `n = gCARD g ⇒ XX` ["XX"] >> strip_tac >>
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
  `a1.iter ≠ a2.iter` by metis_tac[iter_11] >>
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
  ``(∀a f s. ap (a with iter updated_by f) s = ap a s) ⇒
    ∀s0 G s.
      genEvalG ap s0 G s ⇒
      ∀f. INJ f (iterations G) UNIV ⇒ genEvalG ap s0 (imap f G) s``,
  strip_tac >> Induct_on `genEvalG` >> rpt strip_tac >> simp[] >>
  match_mp_tac (genEvalG_rules |> SPEC_ALL |> CONJUNCT2) >>
  dsimp[imap_edges] >>
  qexists_tac `a` >> simp[] >>
  `∀a1 a2. a1 ∈ G ∧ a2 ∈ G ⇒
           (a1 with iter updated_by f = a2 with iter updated_by f ⇔
            a1 = a2)`
    by (rpt strip_tac >> fds[INJ_THM, iterations_thm] >> simp[EQ_IMP_THM] >>
        simp[action_component_equality]) >>
  reverse conj_tac
  >- (`INJ f (iterations (G \\ a)) UNIV` by fds[INJ_THM, iterations_thm] >>
      `imap f G \\ (a with iter updated_by f) = imap f (G \\ a)`
         suffices_by simp[] >>
      dsimp[graph_equality, imap_edges, EQ_IMP_THM, IN_imap] >> csimp[] >>
      rpt strip_tac
      >- (ntac 2 (pop_assum mp_tac) >> imp_res_tac IN_edges >> simp[] >>
          metis_tac[]) >>
      metis_tac[IN_edges]) >>
  rpt gen_tac >>
  qmatch_rename_tac `a0 ∈ G ⇒ a1' -<G>/-> a2' ∨ XX` ["XX"] >> strip_tac >>
  Cases_on `a1' -<G>-> a2'` >> simp[] >> metis_tac[IN_edges]);

(* ----------------------------------------------------------------------
    Define a gEVAL constant to be the function of the relation
   ---------------------------------------------------------------------- *)

val gEVAL_def = new_specification(
  "gEVAL_def", ["gEVAL"],
  genEvalG_total |> SPEC_ALL |> Q.GENL [`g`, `s0`, `ap`]
                 |> SIMP_RULE bool_ss[SKOLEM_THM]);

val gEVAL_thm = store_thm(
  "gEVAL_thm",
  ``(∀a1 a2 s. ¬touches a1 a2 ∧ a1.iter ≠ a2.iter ⇒
               ap a2 (ap a1 s) = ap a1 (ap a2 s)) ⇒
    (∀s0. gEVAL ap s0 emptyG = s0) ∧
    (∀a s0. a.iter ∉ iterations g ⇒
            gEVAL ap s0 (a ⊕ g) = gEVAL ap (ap a s0) g)``,
  rpt strip_tac
  >- (`genEvalG ap s0 emptyG s0` by simp[genEvalG_rules] >>
      metis_tac[gEVAL_def, genEvalG_det]) >>
  `a ∈ a ⊕ g` by simp[] >>
  `a ∉ g` by (strip_tac >> fs[iterations_thm]) >>
  `∀a'. a' ∈ a ⊕ g ⇒ a' -<a ⊕ g>/-> a`
     by (dsimp[add_action_edges] >> metis_tac[IN_edges]) >>
  `genEvalG ap (ap a s0) g (gEVAL ap (ap a s0) g)` by metis_tac[gEVAL_def] >>
  `(a ⊕ g) \\ a = g`
    by (csimp[graph_equality, add_action_edges] >> metis_tac[IN_edges]) >>
  `genEvalG ap s0 (a ⊕ g) (gEVAL ap (ap a s0) g)`
    by metis_tac[genEvalG_rules] >>
  metis_tac[genEvalG_det, gEVAL_def]);

val graph_ind = store_thm(
  "graph_ind",
  ``∀P. P emptyG ∧ (∀a g. P g ∧ a ∉ g ∧ a.iter ∉ iterations g ⇒ P (a ⊕ g)) ⇒
        ∀g. P g``,
  rpt strip_tac >>
  Induct_on `gCARD g` >> simp[] >> rpt strip_tac >>
  `ag_nodes g ≠ ∅` by (strip_tac >> fs[]) >>
  `∃a. a ∈ g ∧ ∀b. b -<g>/-> a`
     by metis_tac[nonempty_wfG_has_points, IN_edges] >>
  qmatch_assum_rename_tac `SUC n = gCARD g` [] >>
  `gCARD (g \\ a) = n` by simp[gCARD_gDELETE] >>
  `a ⊕ (g \\ a) = g`
    by (dsimp[graph_equality, iterations_thm, gDELETE_edges,
              add_action_edges] >> conj_tac
        >- metis_tac[iter_11] >>
        dsimp[EQ_IMP_THM] >> rpt strip_tac
        >- metis_tac[touching_actions_link] >>
        qmatch_assum_rename_tac `a1 -<g>-> a2` [] >>
        `a ≠ a2` by metis_tac[] >> simp[] >>
        Cases_on `a = a1` >> simp[] >>
        metis_tac[IN_edges, iter_11]) >>
  `a.iter ∉ iterations (g \\ a)`
    by (dsimp[iterations_thm] >> metis_tac[iter_11]) >>
  `P (g \\ a)` by metis_tac[] >>
  `a ∉ g \\ a` by simp[] >>
  `P (a ⊕ g \\ a)` by metis_tac[] >>
  metis_tac[]);

(* ----------------------------------------------------------------------
    Merging graphs, second graph is added to the "back" of the first.
   ---------------------------------------------------------------------- *)

val add_postaction_commutes = store_thm(
  "add_postaction_commutes",
  ``∀a1 a2 g. ¬touches a1 a2 ∧ a1.iter ≠ a2.iter ⇒
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
     a ∈ g1 ∨ a.iter ∉ iterations g1 ∧ a ∈ g2``,
  map_every qid_spec_tac [`a`, `g1`, `g2`] >> ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm] >> rpt gen_tac >> strip_tac >>
  dsimp[EQ_IMP_THM] >> rpt strip_tac >>
  qmatch_assum_rename_tac `b.iter ∉ iterations g1` [] >>
  Cases_on `a.iter = b.iter` >> fs[iterations_thm]);

val iterations_merge_graph = store_thm(
  "iterations_merge_graph[simp]",
  ``iterations (merge_graph g1 g2) = iterations g1 ∪ iterations g2``,
  dsimp[iterations_thm, EXTENSION] >> metis_tac[iter_11]);

val add_postaction_empty = store_thm(
  "add_postaction_empty[simp]",
  ``add_postaction a emptyG = a ⊕ emptyG``,
  simp[graph_equality, add_postaction_edges, add_action_edges]);

val add_action_add_postaction_ASSOC = store_thm(
  "add_action_add_postaction_ASSOC",
  ``a.iter ≠ b.iter ⇒
    add_postaction b (a ⊕ g) = a ⊕ (add_postaction b g)``,
  dsimp[graph_equality, IN_add_postaction, add_postaction_edges,
        add_action_edges, iterations_thm] >> metis_tac[]);

val merge_graph_postaction_ASSOC = store_thm(
  "merge_graph_postaction_ASSOC",
  ``merge_graph g1 (add_postaction a g2) =
    add_postaction a (merge_graph g1 g2)``,
  Cases_on `a.iter ∈ iterations g2`
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
  ``a.iter ∉ iterations g2 ⇒ merge_graph (a ⊕ g1) g2 = a ⊕ merge_graph g1 g2``,
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

val add_postaction_EQ_add_action = store_thm(
  "add_postaction_EQ_add_action",
  ``∀g. (∀b. b ∈ g ⇒ ¬touches a b) ⇒ add_postaction a g = a ⊕ g``,
  simp[graph_equality, add_postaction_edges, add_action_edges, EQ_IMP_THM] >>
  rpt strip_tac >> simp[] >> rw[] >> metis_tac[touches_SYM]);

val nontouching_merge_COMM = store_thm(
  "nontouching_merge_COMM",
  ``∀g1 g2. ¬gtouches g1 g2 ∧ DISJOINT (iterations g1) (iterations g2) ⇒
            merge_graph g1 g2 = merge_graph g2 g1``,
  ho_match_mp_tac graph_ind >> simp[merge_graph_thm] >> rpt strip_tac >>
  `add_postaction a g2 = a ⊕ g2` by metis_tac[add_postaction_EQ_add_action] >>
  simp[merge_graph_addaction_ASSOC] >> metis_tac[]);

val _ = export_theory();
