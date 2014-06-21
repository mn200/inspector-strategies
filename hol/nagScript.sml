open HolKernel Parse boolLib bossLib;
open lcsymtacs

open pred_setTheory
open listTheory
open pairTheory
open actionGraphTheory
open cardinalTheory

(* nag = "Nested Action Graph" *)
val _ = new_theory "nag";

(* want to create a type NG satisfying equation

     NG ≈ δ + (α,NG,β) action_graph

   first step is to show a bijection between a graph and a list of its
   nodes.

*)

val FOLDR_add_action_SURJ = store_thm(
  "FOLDR_add_action_SURJ",
  ``SURJ (FOLDR add_action emptyG) UNIV UNIV``,
  simp[SURJ_DEF] >> ho_match_mp_tac graph_ind >> conj_tac
  >- (qexists_tac `[]` >> simp[]) >>
  simp[PULL_EXISTS] >> map_every qx_gen_tac [`a`, `l`] >> strip_tac >>
  qexists_tac `a::l` >> simp[]);

val INFINITE_actions = store_thm(
  "INFINITE_actions[simp]",
  ``INFINITE univ(:(α,β,γ)action)``,
  simp[infinite_num_inj] >>
  qexists_tac `λn. <| reads := GENLIST (K ARB) n; writes := [];
                      data := ARB; ident := ARB |>` >>
  simp[INJ_DEF] >> simp[LIST_EQ_REWRITE]);

val graph_cardEQ_nodes = store_thm(
  "graph_cardEQ_nodes",
  ``univ(:(α,β,γ)action_graph) ≈ univ(:(α,β,γ)action)``,
  match_mp_tac cardleq_ANTISYM >> conj_tac
  >- (assume_tac (MATCH_MP INFINITE_A_list_BIJ_A INFINITE_actions) >>
      `univ(:(α,β,γ) action_graph) ≼ univ(:(α,β,γ) action list)`
        suffices_by metis_tac[CARDEQ_CARDLEQ, cardeq_REFL, UNIV_list] >>
      simp[cardleq_SURJ] >> metis_tac[FOLDR_add_action_SURJ]) >>
  simp[cardleq_def] >> qexists_tac `λa. a ⊕ emptyG` >>
  simp[INJ_DEF, graph_equality] >> metis_tac[]);

val FINITE_list = store_thm(
  "FINITE_list[simp]",
  ``FINITE (list s) ⇔ s = ∅``,
  eq_tac >> simp[] >>
  simp[list_def] >> spose_not_then strip_assume_tac >>
  `∃e t. s = e INSERT t ∧ e ∉ t` by metis_tac[SET_CASES] >>
  qpat_assum `FINITE ss` mp_tac >> simp[infinite_num_inj] >>
  qexists_tac `λn. GENLIST (K e) n` >>
  simp[INJ_DEF, MEM_GENLIST, PULL_EXISTS] >>
  simp[LIST_EQ_REWRITE]);

val nodes_cardEQ_CROSS = store_thm(
  "nodes_cardEQ_CROSS",
  ``univ(:(α,β,γ) action) ≈ univ(:β list) × univ(:α) × univ(:γ)``,
  `univ(:(α,β,γ) action) ≈ univ(:β list) × univ(:β list) × univ(:α) × univ(:γ) ∧
   univ(:β list) × univ(:β list) × univ(:α) × univ(:γ) ≈
   univ(:β list) × univ(:α) × univ(:γ)` suffices_by metis_tac[cardeq_TRANS] >>
  conj_tac
  >- (simp[BIJ_DEF, cardeq_def] >>
      qexists_tac `λa. (((a.reads, a.writes), a.data), a.ident)` >>
      simp[INJ_DEF, SURJ_DEF] >> conj_tac >- simp[action_component_equality] >>
      simp[FORALL_PROD] >> map_every qx_gen_tac [`rds`, `wts`, `data`, `i`] >>
      qexists_tac `<| reads := rds; writes := wts; data := data; ident := i|>` >>
      simp[]) >>
  `univ(:β list) × univ(:β list) ≈ univ(:β list)`
    suffices_by metis_tac[CARDEQ_CROSS,cardeq_REFL] >>
  simp[SET_SQUARED_CARDEQ_SET]);

val tau = ``:(γ # β list # δ) inf``
val aqtau = ty_antiq tau

val eqn1 = MATCH_MP cardeq_TRANS (CONJ graph_cardEQ_nodes nodes_cardEQ_CROSS)
                    |> INST_TYPE [alpha |-> tau]

val univblist = prove(
  ``univ(:β list) <<= UNIV: ^aqtau set``,
  simp[INJ_DEF, cardleq_def] >>
  qexists_tac `λbl : β list. INR (ARB, bl, ARB)` >>
  simp[]);

val univg = prove(
  ``univ(:γ) <<= UNIV : ^aqtau set``,
  simp[INJ_DEF, cardleq_def] >>
  qexists_tac `λg : γ. INR (g, ARB, ARB)` >>
  simp[]);

val univtau = ISPEC ``UNIV : ^aqtau set`` cardleq_REFL

val tau_squared =
    ISPEC ``UNIV : ^aqtau set`` (GEN_ALL SET_SQUARED_CARDEQ_SET)
          |> SIMP_RULE (srw_ss()) []

val ublist_utau_leq_tau2 =
    MATCH_MP (GEN_ALL CARDLEQ_CROSS_CONG) (CONJ univblist univtau)

val cardeqRleq = prove(
  ``∀s t1 t2. t1 =~ t2 /\ s <<= t1 ⇒ s <<= t2``,
  metis_tac [CARDEQ_CARDLEQ, cardeq_REFL])

val cardeqLleq = prove(
  ``∀s t1 t2. t1 =~ t2 /\ t1 <<= s ⇒ t2 <<= s``,
  metis_tac [CARDEQ_CARDLEQ, cardeq_REFL])

val c12 = MATCH_MP cardeqRleq (CONJ tau_squared ublist_utau_leq_tau2)

val c123 = MATCH_MP cardeqRleq
                    (CONJ tau_squared
                          (MATCH_MP (GEN_ALL CARDLEQ_CROSS_CONG) (CONJ c12 univg)))

val tau_ag = ``:(^tau, β, γ) action_graph``
val aqtau_ag = ty_antiq tau_ag

val aglt = MATCH_MP cardeqLleq (CONJ (ONCE_REWRITE_RULE [cardeq_SYM] eqn1) c123)

val sumlt1 = prove(
  ``UNIV : (^aqtau_ag + δ) set <<= {T;F} CROSS UNIV : ^aqtau set``,
  simp[cardleq_def, INJ_DEF] >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [INJ_THM, cardleq_def] aglt) >>
  qexists_tac `λs. case s of INL t => (T,f t) | INR d => (F, INR(ARB,ARB,d))` >>
  simp[] >> map_every qx_gen_tac [`x`, `y`] >>
  Cases_on `x` >> Cases_on `y` >> simp[]);

val infinite_tau = prove(``INFINITE (UNIV : ^aqtau set)``, simp[])

val lemma1 =
    MATCH_MP cardeqRleq (CONJ (MATCH_MP SET_SUM_CARDEQ_SET infinite_tau
                                        |> CONJUNCT1
                                        |> ONCE_REWRITE_RULE [cardeq_SYM])
                              sumlt1)

val lemma2 = prove(
   ``UNIV : ^aqtau set <<= UNIV : (^aqtau_ag + δ) set``,
  simp[cardleq_def, INJ_DEF] >>
  qexists_tac `λd. INL (<| writes := []; reads := []; data := d; ident := ARB |> ⊕
                        emptyG)` >>
  simp[] >> map_every qx_gen_tac [`x`, `y`] >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) [EXTENSION] o Q.AP_TERM `ag_nodes`) >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM]) >>
  strip_tac >> fs[]);

val equivalence = MATCH_MP cardleq_ANTISYM (CONJ lemma1 lemma2)

val mkdest_def = new_specification ("mkdest_def",
  ["cmk", "cdest"],
  equivalence |> SIMP_RULE (srw_ss()) [cardeq_def, BIJ_IFF_INV])

val (cwf_rules, cwf_ind, cwf_cases) = Hol_reln`
  (∀d. cwf (cmk (INR d))) ∧
  (∀g. (∀a. a ∈ g ⇒ cwf a.data) ⇒ cwf (cmk (INL g)))
`;

val cwf_nonempty = prove(
  ``∃x. cwf x``,
  qexists_tac `cmk (INR d)` >> simp[cwf_rules])

val (cwfdmapR_rules, cwfdmapR_ind, cwfdmapR_cases) = Hol_reln`
  (∀d. cwfdmapR df gf (cmk (INR d)) (df d)) ∧

  (∀g rg.
     idents g = idents rg ∧
     (∀i j. i -<g>#-> j ⇔ i -<rg>#-> j) ∧
     (∀i. i ∈ idents g ⇒
          cwfdmapR df gf (g ' i).data (rg ' i).data ∧
          (g ' i).reads = (rg ' i).reads ∧
          (g ' i).writes = (rg ' i).writes)
    ⇒
     cwfdmapR df gf (cmk (INL g)) (gf rg))
`;

val dR_rules = SIMP_RULE (srw_ss()) [FORALL_AND_THM] cwfdmapR_rules

val polydata_upd_ident = store_thm(
  "polydata_upd_ident[simp]",
  ``(polydata_upd f a).ident = a.ident``,
  simp[polydata_upd_def]);

val polydata_upd_reads_writes = store_thm(
  "polydata_upd_reads_writes[simp]",
  ``(polydata_upd f a).reads = a.reads ∧ (polydata_upd f a).writes = a.writes``,
  simp[polydata_upd_def]);

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

val dgmap_ilink = store_thm(
  "dgmap_ilink[simp]",
  ``∀g. i -<dgmap f g>#-> j ⇔ i -<g>#-> j``,
  ho_match_mp_tac graph_ind >> simp[ilink_add_action] >> rpt strip_tac >>
  csimp[]);

val cwfdmapR_total = store_thm(
  "cwfdmapR_total",
  ``∀d. cwf d ⇒ ∃r. cwfdmapR df gf d r``,
  ho_match_mp_tac cwf_ind >> conj_tac
  >- metis_tac[cwfdmapR_rules] >>
  qx_gen_tac `g` >> strip_tac >> fs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  qexists_tac `gf (dgmap f g)` >>
  match_mp_tac (CONJUNCT2 dR_rules) >> simp[] >> rpt strip_tac >>
  simp[polydata_upd_def] >> first_x_assum match_mp_tac >>
  fs[idents_thm,fmap_inverts_ident]);

val cmk_11 = prove(
  ``(cmk x = cmk y) ⇔ x = y``,
  metis_tac[mkdest_def]);

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

val cwfdmapR_unique = store_thm(
  "cwfdmapR_unique",
  ``∀d r1. cwfdmapR df dg d r1 ⇒ ∀r2. cwfdmapR df dg d r2 ⇒ (r2 = r1)``,
  Induct_on `cwfdmapR` >> conj_tac >- (simp[Once cwfdmapR_cases, cmk_11]) >>
  map_every qx_gen_tac [`g`, `rg`] >> strip_tac >>
  simp[Once cwfdmapR_cases, cmk_11] >> simp[PULL_EXISTS] >>
  qx_gen_tac `rg'` >> strip_tac >> AP_TERM_TAC >>
  simp[graph_ident_equality] >> qx_gen_tac `i` >> strip_tac >>
  Q.UNDISCH_THEN `idents g = idents rg` mp_tac >>
  Q.UNDISCH_THEN `idents rg = idents rg'` mp_tac >>
  rpt strip_tac >> fs[] >> res_tac >>
  simp[action_component_equality]);

val cwfdmapf_def = Define`
  cwfdmapf df dg x = @r. cwfdmapR df dg x r
`;

val cwfdmapf_INR = prove(
  ``cwfdmapf df dg (cmk (INR d)) = df d``,
  simp[cwfdmapf_def, Once cwfdmapR_cases, cmk_11]);

val _ = overload_on("adata", ``action_data``)

val cwfdmapf_INL = prove(
  ``cwf (cmk (INL g)) ⇒
    cwfdmapf df dg (cmk (INL g)) = dg (dgmap (cwfdmapf df dg o adata) g)``,
  simp[cwfdmapf_def] >> strip_tac >> SELECT_ELIM_TAC >> conj_tac
  >- metis_tac[cwfdmapR_total] >> qx_gen_tac `r` >>
  simp[Once cwfdmapR_cases, SimpL ``$==>``] >> simp[cmk_11] >>
  disch_then (qx_choose_then `rg` strip_assume_tac) >> rw[] >> AP_TERM_TAC >>
  simp[graph_ident_equality] >> qx_gen_tac `i` >> strip_tac >>
  simp[polydata_upd_def, action_component_equality] >>
  `cwfdmapR df dg (g ' i).data (rg ' i).data` by metis_tac[] >>
  simp[cwfdmapf_def] >> SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
  metis_tac[cwfdmapR_unique]);

val nnode as {term_ABS_t,term_REP_t,...} =
    newtypeTools.rich_new_type ("nnode", cwf_nonempty)

val nnodeREC_def = Define`
  nnodeREC df dg n = cwfdmapf df dg (^term_REP_t n)
`;

val DN_def = Define`
  DN d = ^term_ABS_t (cmk (INR d))
`;

val nnodeREC_DN = store_thm(
  "nnodeREC_DN",
  ``nnodeREC df dg (DN d) = df d``,
  simp[nnodeREC_def, DN_def, #repabs_pseudo_id nnode, cwf_rules, cwfdmapf_INR]);

val DG_def = Define`
  DG (g : ((α,β,γ)nnode, β, α) action_graph) =
   ^term_ABS_t (cmk (INL (dgmap (^term_REP_t o adata) g)))
`;

val dgmap_dgmap = store_thm(
  "dgmap_dgmap[simp]",
  ``∀G. dgmap (f o adata) (dgmap (g o adata) G) = dgmap ((f o g) o adata) G``,
  ho_match_mp_tac graph_ind >> simp[polydata_upd_def]);

val nnodeREC_DG = store_thm(
  "nnodeREC_DG",
  ``nnodeREC df dg (DG g) = dg (dgmap (nnodeREC df dg o adata) g)``,
  simp[nnodeREC_def, DG_def] >>
  `cwf (cmk (INL (dgmap (nnode_REP o adata) g)))`
    by (match_mp_tac (CONJUNCT2 cwf_rules) >> simp[IN_dgmap, PULL_EXISTS] >>
        simp[polydata_upd_def, #termP_term_REP nnode]) >>
  simp[#repabs_pseudo_id nnode] >>
  simp[cwfdmapf_INL, cmk_11] >> simp[nnodeREC_def, combinTheory.o_DEF]);

val _ = type_abbrev("nag0", ``:(('ids, 'rws, 'd)nnode, 'rws, 'ids) action_graph``)

val _ = export_theory();
