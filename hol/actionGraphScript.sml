open HolKernel Parse boolLib bossLib;

open primitivesTheory pred_setTheory listRangeTheory listTheory
open finite_mapTheory
open lcsymtacs
fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun dsimp thl = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) thl
fun csimp thl = asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss) thl

val _ = new_theory "actionGraph";



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

val _ = Hol_datatype`
  action_graph0 = <|
    nodes : 'a action set;
    edges : 'a action -> 'a action set
  |>
`

val wfG_def = Define`
  wfG G ⇔
      FINITE G.nodes ∧
      (∀a1 a2. G.edges a1 a2 ⇒ touches a1 a2 ∧ a1 ∈ G.nodes ∧ a2 ∈ G.nodes) ∧
      (∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ touches a1 a2 ∧ a1 ≠ a2 ⇒ (¬G.edges a1 a2 ⇔ G.edges a2 a1)) ∧
      (∀a1 a2. a1 ∈ G.nodes ∧ a2 ∈ G.nodes ∧ G.edges⁺ a1 a2 ⇒ ¬G.edges⁺ a2 a1) ∧
      INJ (λa. a.iter) G.nodes univ(:num)
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
  ``(∃g:'a action_graph0. wfEQ g g) ∧
    (∀x y:'a action_graph0. wfEQ x y ⇔ wfEQ x x ∧ wfEQ y y ∧ wfEQ x = wfEQ y)``,
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

fun gen th = let
  val t = concl th
  val fvs = filter (fn v => type_of v = ``:'a action_graph0``) (free_vars t)
  fun gen1 (t, th) =
      th |> ADD_ASSUM ``^t IN respects wfEQ``
         |> DISCH_ALL
         |> GEN t
         |> SIMP_RULE bool_ss [GSYM RES_FORALL_THM]
in
  foldl gen1 th fvs
end

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

val IN_add_action0 = prove(
  ``x ∈ (add_action0 a G).nodes <=>
    a.iter ∉ iterations0 G ∧ x = a ∨ x ∈ G.nodes``,
  rw[add_action0_def]);

val add_action0_edges = prove(
  ``(add_action0 a G).edges a1 a2 ⇔
      a.iter ∉ iterations0 G ∧ a1 = a ∧ a2 ∈ G.nodes ∧ touches a1 a2 ∨
      G.edges a1 a2``,
  rw[add_action0_def] >> metis_tac[]);

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
    by (rpt strip_tac >> simp[theorem "action_component_equality", Abbr`f'`] >>
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
     iterations_thm, FDOM_fmap, fmap_add_action, IN_edges,
     IN_gDELETE, nodes_gDELETE, gDELETE_edges, gDELETE_commutes,
     imap_emptyG, IN_imap, imap_edges, touching_actions_link, imap_id] =
define_quotient {
  types = [{name = "action_graph", equiv = wfEQ_equiv}],
  defs = [("emptyG",``emptyG0``),
          ("iterations", ``iterations0``),
          ("ag_nodes", ``action_graph0_nodes``),
          ("ag_edges", ``action_graph0_edges``),
          ("add_action", ``add_action0``),
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
          ("iterations_thm", iterations0_def),
          ("FDOM_fmap", FDOM_fmap0),
          ("fmap_add_action", fmap0_add_action0),
          ("IN_edges", mkwfeq IN_edges0),
          ("IN_gDELETE", mkwfeq IN_gDELETE0),
          ("nodes_gDELETE", nodes_delete),
          ("gDELETE_edges", gDELETE0_edges),
          ("gDELETE_commutes", gDELETE0_commutes),
          ("imap_emptyG", imap_emptyG0),
          ("IN_imap", IN_imap0),
          ("imap_edges", imap0_edges),
          ("touching_actions_link", mkwfeq (GEN_ALL touching_actions_link0)),
          ("imap_id", imap0_id)],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfEQ_emptyG0, simple_rsp ``action_graph0_nodes``,
              simple_rsp ``action_graph0_edges``,
              simple_rsp ``fmap0``, wfEQ_delete,
              simple_rsp ``iterations0``, wfEQ_add_action0,
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

val _ = overload_on ("flip_add_action", ``\x y. add_action y x``)
val _ = set_mapped_fixity {fixity = Infixl 500, term_name = "flip_add_action",
                           tok = "⊕"}

val _ = overload_on ("\\\\", ``gDELETE``)

val _ = overload_on ("IN", ``\a g. a IN ag_nodes g``)
val _ = overload_on ("NOTIN", ``\a g. ~(a IN ag_nodes g)``)

val _ = export_rewrites ["edges_WF", "IN_add_action", "IN_imap", "emptyG_nodes",
                         "emptyG_edges", "nodes_gDELETE", "nodes_FINITE",
                         "gDELETE_edges", "edges_irrefl"]

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

val gCARD_EQ_0 = store_thm(
  "gCARD_EQ_0",
  ``gCARD G = 0 ⇔ G = emptyG``,
  simp[EQ_IMP_THM] >> rpt strip_tac >> fs[] >>
  simp[graph_equality] >> fs[CARD_EQ_0] >>
  metis_tac[IN_edges, NOT_IN_EMPTY]);
val _ = export_rewrites ["gCARD_EQ_0"]


val gCARD_gDELETE = store_thm(
  "gCARD_gDELETE",
  ``a ∈ G ⇒ gCARD (G \\ a) = gCARD G - 1``,
  simp[]);
val _ = export_rewrites ["gCARD_gDELETE"]

val IN_emptyG = store_thm(
  "IN_emptyG",
  ``a ∈ emptyG ⇔ F``,
  simp[]);

val GSPEC_CONG = store_thm(
  "GSPEC_CONG",
  ``(!x. SND (f x) = h x) ∧ (!x. h x ⇒ FST (f x) = g x) ⇒ GSPEC f = IMAGE g h``,
  simp[GSPECIFICATION, EXTENSION] >> rpt strip_tac >> eq_tac >> strip_tac
  >- (qmatch_assum_rename_tac `(a,T) = f b` [] >>
      rpt (first_x_assum (qspec_then `b` mp_tac)) >>
      pop_assum (SUBST_ALL_TAC o SYM) >> simp[SPECIFICATION] >>
      metis_tac[]) >>
  rw[] >> fs[SPECIFICATION] >>
  qmatch_assum_rename_tac `h y` [] >> qexists_tac `y` >>
  Cases_on `f y` >>
  rpt (first_x_assum (qspec_then `y` mp_tac)) >> simp[]);
val _ = DefnBase.export_cong "GSPEC_CONG"

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


val _ = export_theory();
