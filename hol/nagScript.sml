open HolKernel Parse boolLib bossLib;

open lcsymtacs
open boolSimps

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

val _ = overload_on("adata", ``action_data``)

val (cwf_rules, cwf_ind, cwf_cases) = Hol_reln`
  (∀d. cwf (cmk (INR d))) ∧
  (∀g. (∀d. d ∈ IMAGE adata (ag_nodes g) ⇒ cwf d) ⇒ cwf (cmk (INL g)))
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
     cwfdmapR df gf (cmk (INL g)) (gf g rg))
`;

val dR_rules = SIMP_RULE (srw_ss()) [FORALL_AND_THM] cwfdmapR_rules


val cwfdmapR_total = store_thm(
  "cwfdmapR_total",
  ``∀d. cwf d ⇒ ∃r. cwfdmapR df gf d r``,
  ho_match_mp_tac cwf_ind >> conj_tac
  >- metis_tac[cwfdmapR_rules] >>
  qx_gen_tac `g` >> strip_tac >> fs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  qexists_tac `gf g (dgmap f g)` >>
  match_mp_tac (CONJUNCT2 dR_rules) >> simp[] >> rpt strip_tac >>
  simp[polydata_upd_def] >> first_x_assum match_mp_tac >>
  fs[idents_thm,fmap_inverts_ident] >> metis_tac[]);

val cmk_11 = prove(
  ``(cmk x = cmk y) ⇔ x = y``,
  metis_tac[mkdest_def]);

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

val cwfdmapf_INL = prove(
  ``cwf (cmk (INL g)) ⇒
    cwfdmapf df dg (cmk (INL g)) = dg g (dgmap (cwfdmapf df dg) g)``,
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
  nnodeREC df dg n = cwfdmapf df (\g. dg (dgmap ^term_ABS_t g)) (^term_REP_t n)
`;

val DN_def = Define`
  DN d = ^term_ABS_t (cmk (INR d))
`;

val nnodeREC_DN = store_thm(
  "nnodeREC_DN[simp]",
  ``nnodeREC df dg (DN d) = df d``,
  simp[nnodeREC_def, DN_def, #repabs_pseudo_id nnode, cwf_rules, cwfdmapf_INR]);

val DG_def = Define`
  DG (g : ((α,β,γ)nnode, β, α) action_graph) =
   ^term_ABS_t (cmk (INL (dgmap ^term_REP_t g)))
`;

val nnodeREC_DG = store_thm(
  "nnodeREC_DG[simp]",
  ``nnodeREC df dg (DG g) = dg g (dgmap (nnodeREC df dg) g)``,
  simp[nnodeREC_def, DG_def] >>
  `cwf (cmk (INL (dgmap nnode_REP g)))`
    by (match_mp_tac (CONJUNCT2 cwf_rules) >> simp[IN_dgmap, PULL_EXISTS] >>
        simp[polydata_upd_def, #termP_term_REP nnode]) >>
  simp[#repabs_pseudo_id nnode] >>
  simp[cwfdmapf_INL, cmk_11] >>
  asm_simp_tac (srw_ss() ++ ETA_ss) [GSYM nnodeREC_def, combinTheory.o_DEF,
                                     #absrep_id nnode]);

val _ = type_abbrev("nag0", ``:(('ids, 'rws, 'd)nnode, 'rws, 'ids) action_graph``)

val nnodeSize_def = Define `
  nnodeSize = nnodeREC (K 1) (λg r. 1 + dgSIGMA I r)
`;

val nnodeSize_thm = store_thm(
  "nnodeSize_thm[simp]",
  ``nnodeSize (DN d) = 1 ∧
    nnodeSize (DG g) = 1 + dgSIGMA I (dgmap nnodeSize g)``,
  simp[nnodeSize_def, nnodeREC_DN, nnodeREC_DG]);

val nagSize_def = Define`
  nagSize (g:(α,β,γ)nag0) = dgSIGMA nnodeSize g
`;

val nnode_CASE_def = Define`
  nnode_CASE n df dg = nnodeREC df (λg r. dg g) n
`;

val nnode_CASE_thm = store_thm(
  "nnode_CASE_thm[simp]",
  ``nnode_CASE (DN d) df dg = df d ∧
    nnode_CASE (DG g) df dg = dg g``,
  simp[nnode_CASE_def, nnodeREC_DG, nnodeREC_DN]);

val nnode_Axiom = store_thm(
  "nnode_Axiom",
  ``∀df dg. ∃f.
      (∀d. f (DN d) = df d) ∧
      (∀g. f (DG g) = dg g (dgmap f g))``,
  rpt gen_tac >> qexists_tac `nnodeREC df dg` >>
  simp[nnodeREC_DN, nnodeREC_DG]);

val forall_nnode = prove(
  ``(!n. P n) ⇔ (∀a. cwf a ⇒ P (nnode_ABS a))``,
  eq_tac >> simp[] >> rpt strip_tac >>
  ONCE_REWRITE_TAC [GSYM (#absrep_id nnode)] >>
  first_x_assum match_mp_tac >> simp[#termP_term_REP nnode]);

val nnode_ind = store_thm(
  "nnode_ind",
  ``∀P. (∀d. P (DN d)) ∧
        (∀g. (∀d. d ∈ IMAGE adata (ag_nodes g) ⇒ P d) ⇒
             P (DG g)) ⇒
        ∀n. P n``,
  simp[DN_def, DG_def, PULL_EXISTS, forall_nnode] >>
  ntac 2 strip_tac >> Induct_on `cwf` >>
  simp[PULL_EXISTS] >> qx_gen_tac `g` >>
  first_x_assum (qspec_then `dgmap nnode_ABS g` mp_tac) >>
  simp[IN_dgmap, PULL_EXISTS, polydata_upd_def]  >>
  rpt strip_tac >>
  `dgmap (nnode_REP o nnode_ABS) g = dgmap I g`
    by (match_mp_tac dgmap_CONG >>
        simp[PULL_EXISTS, #repabs_pseudo_id nnode]) >>
  fs[]);

val _ = TypeBase.write
  (TypeBasePure.gen_datatype_info {ax = nnode_Axiom, ind = nnode_ind,
                                  case_defs = [nnode_CASE_thm]})

val _ = adjoin_to_theory {
  sig_ps = NONE,
  struct_ps = SOME(fn pps => PP.add_string pps "val _ = TypeBase.write \
  \(TypeBasePure.gen_datatype_info {ax = nnode_Axiom, ind = nnode_ind, \
  \case_defs = [nnode_CASE_thm]})")}

val nagSize_thm = store_thm(
  "nagSize_thm[simp]",
  ``nagSize emptyG = 0 ∧
    (a.ident ∉ idents g ⇒
     nagSize (a ⊕ g) =
       1 + (case a.data of DN _ => 0 | DG g0 => nagSize g0) + nagSize g)``,
  simp[nagSize_def] >> Cases_on `adata a` >> simp[]);

val _ = export_theory();
