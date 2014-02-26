open HolKernel Parse boolLib bossLib;

open primitivesTheory pred_setTheory listRangeTheory listTheory
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
  ``!G::respects wfEQ. x ∈ G.nodes ⇒ ¬G.edges x x``,
  simp[wfG_def, wfEQ_def, quotientTheory.respects_def, RES_FORALL_THM, INWR] >> rpt strip_tac >>
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

val add_action_def = Define`
  add_action a G =
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

val wfG_FINITE = store_thm(
  "wfG_FINITE",
  ``!G::respects wfEQ. FINITE G.nodes``,
  simp[wfG_def, wfEQ_def, quotientTheory.respects_def, INWR, RES_FORALL_THM]);

(*
val wfG_add_action = prove(
  ``wfG G ⇒ wfG (add_action a G)``,
  rw[add_action_def] >> fs[wfG_def] >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (fs[iterations0_def] >> metis_tac[TC_in_R, touches_SYM])
  >- (fs[iterations0_def] >> metis_tac[TC_in_R, touches_SYM])
*)


fun mk(s,t) = {def_name = s ^ "_def", fname = s, fixity = NONE, func = t}

val [emptyG_nodes, emptyG_edges, edges_irrefl, graph_equality,
     edges_WF, nodes_FINITE] =
quotientLib.define_quotient_types_full {
  types = [{name = "action_graph", equiv = wfEQ_equiv}],
  defs = [mk("emptyG",``emptyG0``),
          mk("iterations", ``iterations0``),
          mk("ag_nodes", ``action_graph0_nodes``),
          mk("ag_edges", ``action_graph0_edges``)],
  old_thms = [emptyG0_nodes, emptyG0_edges, wfG_irrefl, graph0_equality,
              wfG_WF, wfG_FINITE],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfEQ_emptyG0, simple_rsp ``action_graph0_nodes``,
              simple_rsp ``action_graph0_edges``,
              simple_rsp ``iterations0``],
  tyop_equivs = [],
  tyop_quotients = [],
  tyop_simps = []}

val _ = augment_srw_ss [rewrites [edges_WF]]

val nonempty_wfG_has_points = store_thm(
  "nonempty_wfG_has_points",
  ``ag_nodes G ≠ ∅ ⇒
    ∃e. e ∈ ag_nodes G ∧ ∀e'. e' ∈ ag_nodes G ⇒ ¬ag_edges G e' e``,
  rpt strip_tac >>
  `WF (ag_edges G)` by simp[] >>
  pop_assum mp_tac >> REWRITE_TAC [relationTheory.WF_DEF] >>
  simp[IN_DEF] >>
  pop_assum mp_tac >> simp[GSYM MEMBER_NOT_EMPTY, IN_DEF] >>
  metis_tac[]);

val _ = export_theory();
