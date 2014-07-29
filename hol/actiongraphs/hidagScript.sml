open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory pairTheory
open lcsymtacs
open ndagTheory actionTheory dagTheory
open bagTheory

val _ = new_theory "hidag";

val (wfnag_rules, wfnag_ind, wfnag_cases) = Hol_reln`
  wfnag ε ∧

  (∀a g0 g.
      a.data = DG g0 ∧ wfnag g0 ∧
      a.writes = [] ∧ a.reads = [] ∧
      wfnag g
     ⇒
      wfnag (a <+ g)) ∧

  (∀a d g.
      a.data = DN d ∧ wfnag g ⇒ wfnag(a <+ g))
`;

val wfnag_empty = prove(
  ``wfnag ε``,
  simp[wfnag_rules])
val _ = augment_srw_ss [rewrites [wfnag_empty]]

val wfnag_rule = prove(
  ``wfnag (a <+ ε) ∧ wfnag g ⇒ wfnag (a <+ g)``,
  Cases_on `wfnag g` >> simp[] >>
  ONCE_REWRITE_TAC [wfnag_cases] >> simp[] >> metis_tac[]);


(*val (wfgEQ0_rules, wfgEQ0_ind, wfgEQ0_cases) = Hol_reln`
  wfgEQ0 ε ε ∧

  (∀a1 a2 d1:(α,β)ndag0 d2.
      wfnEQ0 a1 a2 ∧ wfgEQ0 d1 d2
    ⇒
      wfgEQ0 (a1 <+ d1) (a2 <+ d2)) ∧

  (∀a1 a2.
     set a1.writes = set a2.writes ∧
     set a1.reads = set a2.reads ∧
     (∀g01. a1.data = DG g01 ⇒
            ∃g02. a2.data = DG g02 ∧ wfgEQ0 g01 g02) ∧
     (∀d. a1.data = DN d ⇒ a2.data = DN d)
    ⇒
     wfnEQ0 a1 a2)
`;

val wfgEQ0_refl = prove(
  ``∀d. wfgEQ0 d d``,
  gen_tac >> completeInduct_on `nagSize d` >> qx_gen_tac `d` >>
  rw[] >>
  Q.ISPEC_THEN `d` strip_assume_tac dag_CASES >>
  simp[wfgEQ0_rules]);

val wfgEQ0_sym = prove(
  ``(∀d1:(α,β)ndag0 d2. wfgEQ0 d1 d2 ⇒ wfgEQ0 d2 d1) ∧
    (∀n1:((β,α)nnode,β)node n2. wfnEQ0 n1 n2 ⇒ wfnEQ0 n2 n1)``,
  Induct_on `wfgEQ0` >> simp[wfgEQ0_rules] >> rpt strip_tac >>
  match_mp_tac (last (CONJUNCTS wfgEQ0_rules)) >> simp[] >>
  Cases_on `n1.data` >> fs[]);

val wfgEQ0_empty = prove(
  ``(wfgEQ0 ε d ⇔ d = ε) ∧ (wfgEQ0 d ε ⇔ d = ε)``,
  ONCE_REWRITE_TAC [wfgEQ0_cases] >> simp[]);

val wfn_rws = prove(
  ``wfnEQ0 a1 a2 ⇒
    set a1.reads = set a2.reads ∧ set a1.writes = set a2.writes``,
  simp[Once wfgEQ0_cases]);

val eq_add_rule = List.nth(CONJUNCTS wfgEQ0_rules, 1)

val wfgEQ0_dagadd_elim = SIMP_RULE (srw_ss()) [PULL_FORALL]
                                   (CONJUNCT1 (prove(
  ``(∀d1:(α,β)ndag0 d2.
       wfgEQ0 d1 d2 ⇒
       ∀a1 d10.
         d1 = a1 <+ d10 ⇒
         ∃a2 d20. d2 = a2 <+ d20 ∧ wfgEQ0 d10 d20 ∧
                  wfnEQ0 a1 a2) ∧
    (∀n1 n2:((β,α)nnode,β)node. wfnEQ0 n1 n2 ⇒ T)``,
  Induct_on `wfgEQ0` >> simp[] >> qx_genl_tac [`n1`, `n2`, `d1`, `d2`] >>
  strip_tac >> qx_genl_tac [`a1`, `d10`] >>
  simp[dagAdd_11_thm] >> strip_tac >> dsimp[] >- rw[] >>
  disj2_tac >>
  first_x_assum (qspecl_then [`a1`, `g0`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`a2'`, `d20`] strip_assume_tac) >>
  rw[] >> map_every qexists_tac [`a2'`, `d20`] >> simp[] >> reverse conj_tac
  >- (match_mp_tac eq_add_rule >> simp[]) >>
  qpat_assum `x ≁ₜ y` mp_tac >> imp_res_tac wfn_rws >>
  simp[touches_def])))

val wfgEQ0_trans = prove(
  ``(∀d1:(α,β)ndag0 d2. wfgEQ0 d1 d2 ⇒ ∀d3. wfgEQ0 d2 d3 ⇒ wfgEQ0 d1 d3) ∧
    (∀n1 n2:((β,α)nnode,β)node.
      wfnEQ0 n1 n2 ⇒ ∀n3. wfnEQ0 n2 n3 ⇒ wfnEQ0 n1 n3)``,
  Induct_on `wfgEQ0` >> simp[wfgEQ0_empty] >> rpt strip_tac
  >- (imp_res_tac wfgEQ0_dagadd_elim >> rw[] >>
      match_mp_tac eq_add_rule >> metis_tac[]) >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC [wfgEQ0_cases] >> simp[] >>
  rpt strip_tac >> fs[] >> REV_FULL_SIMP_TAC (srw_ss()) []);
*)
val wfnag_add = SIMP_RULE (srw_ss()) [PULL_FORALL] (prove(
  ``∀d. wfnag d ⇒ ∀a d0. d = a <+ d0 ⇒ wfnag (a <+ ε) ∧ wfnag d0``,
  Induct_on `wfnag` >> simp[dagAdd_11_thm] >> rw[] >> simp[] >>
  metis_tac [wfnag_rules]))

(*val wfgEQ0_grws = prove(
  ``(∀d1:(α,β)ndag0 d2.
       wfgEQ0 d1 d2 ⇒ wfnag d1 ⇒
       wfnag d2 ∧ greads d2 = greads d1 ∧ gwrites d2 = gwrites d1) ∧
    (∀n1 n2:((β,α)nnode, β)node. wfnEQ0 n1 n2 ⇒ wfnag (n1 <+ ε) ⇒ wfnag (n2 <+ ε))``,
  Induct_on `wfgEQ0` >> simp[] >> conj_tac
  >- (qx_genl_tac [`n1`, `n2`, `d1`, `d2`] >> rpt (disch_then strip_assume_tac) >>
      `wfnag d1 ∧ wfnag (n1 <+ ε) ∧ wfnag (n2 <+ ε)` by metis_tac[wfnag_add] >>
      `wfnag d2 ∧ wfnag (n2 <+ d2)` by metis_tac[wfnag_rule] >> simp[] >>
      imp_res_tac wfnag_rws >> simp[] >>
      imp_res_tac wfnag_nreadswrites >> simp[] >>
      imp_res_tac wfn_rws >> simp[]) >>
  rpt gen_tac >> strip_tac >> ONCE_REWRITE_TAC [wfnag_cases] >> simp[] >>
  strip_tac >> fs[]);
*)
val wfgEQ_def = Define`wfgEQ g1 g2 ⇔ g1 = g2 ∧ wfnag g1`;

val wfnEQ_def = Define`wfnEQ n1 n2 ⇔ n1 = n2 ∧ wfnag (n1 <+ ε)`;

val wfgEQ_equiv = store_thm(
  "wfgEQ_equiv",
  ``(∃g:(α,β)ndag0. wfgEQ g g) ∧
    (∀x y:(α,β)ndag0. wfgEQ x y ⇔ wfgEQ x x ∧ wfgEQ y y ∧ wfgEQ x = wfgEQ y)``,
  simp[wfgEQ_def, FUN_EQ_THM, EQ_IMP_THM] >> metis_tac[wfnag_rules])

val hinode_ty = ``:((β,α)nnode, β) node``
val hinode_aty = ty_antiq hinode_ty

val wfnEQ_equiv = prove(
  ``(∃n:^hinode_aty. wfnEQ n n) ∧
    (∀x y:^hinode_aty.
           wfnEQ x y ⇔ wfnEQ x x ∧ wfnEQ y y ∧ wfnEQ x = wfnEQ y)``,
  simp[wfnEQ_def, FUN_EQ_THM, EQ_IMP_THM] >>
  qexists_tac `<| reads := []; writes := []; data := DN ARB; ident := () |>` >>
  simp[wfnag_rules])

val wfnag_dagmerge0 = prove(
  ``∀d1 d2. wfnag d1 ∧ wfnag d2 ⇒ wfnag (dagmerge d1 d2)``,
  `∀d1. wfnag d1 ⇒ ∀d2. wfnag d2 ⇒ wfnag (dagmerge d1 d2)`
    suffices_by metis_tac[] >>
  Induct_on `wfnag` >> simp[] >> metis_tac[wfnag_rules]);

val wfg_dagmerge = prove(
  ``wfgEQ (d1:(α,β)ndag0) d1' ∧ wfgEQ d2 d2' ⇒ wfgEQ (dagmerge d1 d2) (dagmerge d1' d2')``,
  rw[wfnag_dagmerge0, wfgEQ_def]);

val wf_dagadd = prove(
  ``wfnEQ a1 a2 ∧ wfgEQ (g1:(α,β)ndag0) g2 ⇒ wfgEQ (a1 <+ g1) (a2 <+ g2)``,
  simp[wfnEQ_def, wfgEQ_def] >> rw[] >> simp[wfnag_rule]);


(*val wfg_nodebag = prove(
  ``wfgEQ (g1:(α,β)ndag0) g2 ∧ wfnEQ a1 a2 ⇒ nodebag g1 a1 = nodebag g2 a2``,
  simp[wfgEQ_def, wfnEQ_def])*)

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

val ndinst = INST_TYPE [alpha |-> ``:(β,α)nnode``]

val wfn_touches = prove(
  ``wfnEQ a1 a2 ∧ wfnEQ b1 b2 ⇒ (a1 ∼ₜ b1 ⇔ a2 ∼ₜ b2)``,
  simp[wfnEQ_def]);

val HD0_def = Define`
  HD0 rs ws d = <| reads := rs; writes := ws; data := DN d; ident := () |>
`;

val wfnEQ_HD0 = prove(
  ``wfnEQ (HD0 rs ws d) (HD0 rs ws d)``,
  simp[wfnEQ_def, HD0_def, Once wfnag_cases]);

val HG0_def = Define`
  HG0 (g:(α,β)ndag0) : ^hinode_aty =
   <| reads := []; writes := []; data := DG g; ident := () |>
`;

val wfnEQ_HG0 = prove(
  ``wfgEQ (g1:(α,β)ndag0) g2 ⇒ wfnEQ (HG0 g1) (HG0 g2)``,
  simp[wfgEQ_def, wfnEQ_def] >> rw[] >>
  simp[Once wfnag_cases, HG0_def]);

val HG0_11 = prove(
  ``wfnEQ (HG0 g1) (HG0 g2) ⇔ wfgEQ g1 g2``,
  simp[HG0_def, EQ_IMP_THM, RES_FORALL_THM, wfnEQ_def, wfgEQ_def] >> rw[]
  >- (pop_assum mp_tac >> simp[Once wfnag_cases, SimpL ``$==>``]) >>
  simp[Once wfnag_cases]);

val HD0_11 = prove(
  ``wfnEQ (HD0 rs1 ws1 d1 : ^hinode_aty) (HD0 rs2 ws2 d2) ⇔
      rs1 = rs2 ∧ ws1 = ws2 ∧ d1 = d2``,
  simp[wfnEQ_def, HD0_def, wfnag_rules, EQ_IMP_THM]);

val dagAdd_11' = prove(
  ``∀(g2::respects wfgEQ) (g1::respects wfgEQ) (g::respects wfgEQ)
     (b::respects wfnEQ) (a::respects wfnEQ).
       (wfgEQ (a <+ g) (b <+ g) ⇔ wfnEQ a b) ∧
       (wfgEQ (a <+ g1) (a <+ g2) ⇔ wfgEQ g1 g2)``,
  simp[wfgEQ_def, wfnEQ_def, quotientTheory.respects_def,
       combinTheory.W_DEF, RES_FORALL_THM, wfnag_rule]);

val dagAdd_11_thm' = prove(
  ``wfgEQ (a <+ g) (b <+ h) ⇔
      wfnEQ a b ∧ wfgEQ g h ∨
      a ≁ₜ b ∧ ∃g0::respects wfgEQ. wfgEQ g (b <+ g0) ∧ wfgEQ h (a <+ g0)``,
  simp[wfgEQ_def, dagAdd_11_thm, wfnEQ_def, quotientTheory.respects_def,
       combinTheory.W_DEF, RES_EXISTS_THM] >>
  metis_tac [wfnag_rule, wfnag_add])

val hidag_ind0 = prove(
  ``∀ (P :: respects (wfgEQ ===> $=)) (Q :: respects (wfnEQ ===> $=)).
     P ε ∧
     (∀(a::respects wfnEQ) (d::respects wfgEQ). Q a ∧ P d ⇒ P (a <+ d)) ∧
     (∀rs ws d. Q (HD0 rs ws d)) ∧
     (∀d::respects wfgEQ. P d ⇒ Q (HG0 d)) ⇒
     (∀d::respects wfgEQ. P d) ∧ (∀a::respects wfnEQ. Q a)``,
  simp[RES_FORALL_THM, combinTheory.W_DEF, quotientTheory.respects_def,
       quotientTheory.FUN_REL, wfgEQ_def, wfnEQ_def, HD0_def, HG0_def,
       GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] >>
  rpt gen_tac >> strip_tac >>
  `∀d. wfnag d ⇒ P d`
    by (Induct_on `wfnag` >> simp[] >> rpt strip_tac >>
        first_x_assum match_mp_tac >>
        simp[Once wfnag_cases, SimpL ``$/\``] >>
        Q.ISPEC_THEN `a` strip_assume_tac action_literal_nchotomy >>
        rw[] >> fs[oneTheory.one]) >> simp[] >>
  `∀d. wfnag d ⇒ ∀a. d = a <+ ε ⇒ Q a` suffices_by metis_tac[] >>
  Induct_on `wfnag` >> simp[] >> rpt strip_tac >>
  Q.ISPEC_THEN `a` strip_assume_tac action_literal_nchotomy >>
  fs[oneTheory.one]);

val empty_not_hidagAdd0 = prove(
  ``¬wfgEQ ε (a <+ d)``,
  simp[wfgEQ_def]);

val HD_not_HG0 = prove(
  ``¬wfnEQ (HD0 rs ws d) (HG0 g)``,
  simp[wfnEQ_def, HD0_def, HG0_def, action_component_equality]);

val nnode_measure_def = Define`
  nnode_measure =
    nnodeREC (K 1) (λg r. BAG_CARD (nodebag g) + (dagSIGMA I r + 1))
`;

val nag_measure_def = Define`
  nag_measure = dagSIGMA (λn. 1 + nnode_measure n)
`;

val nag_measure_thm = prove(
  ``nag_measure ε = 0 ∧
    nag_measure (a <+ d) =
      nag_measure d + 1 +
      case a.data of
          DN d => 1
        | DG g => 1 + nag_measure g``,
  simp[nag_measure_def,nnode_measure_def] >>
  Cases_on `a.data` >> simp[] >>
  simp[GSYM nnode_measure_def] >>
  simp[GSYM arithmeticTheory.ADD1,
       arithmeticTheory.ADD_CLAUSES] >>
  simp[arithmeticTheory.ADD1] >>
  qid_spec_tac `g` >> pop_assum kall_tac >>
  simp[Once EQ_SYM_EQ] >>
  ho_match_mp_tac dag_ind >> simp[BAG_CARD_THM])

val hinode_size0_def = Define`
  hinode_size0 a = case a.data of DN v => 1 | DG g => 1 + nag_measure g
`;

val hinode_size0_thm = prove(
  ``hinode_size0 (HD0 rs ws d : ^hinode_aty) = 1 ∧
    hinode_size0 (HG0 (g:(α,β)ndag0)) = 1 + nag_measure g``,
  simp[hinode_size0_def, HD0_def, HG0_def]);

val nag_measure_rsp = prove(
  ``wfgEQ (d1:(α,β)ndag0) d2 ⇒ nag_measure d1 = nag_measure d2``,
  simp[wfgEQ_def]);

val hinode_size0_rsp = prove(
  ``wfnEQ (n1: ^hinode_aty) n2 ⇒ hinode_size0 n1 = hinode_size0 n2``,
  simp[wfnEQ_def]);

val nag_measure_thm' = prove(
  ``nag_measure ε = 0 ∧
    nag_measure (a <+ d : (α,β)ndag0) = hinode_size0 a + nag_measure d + 1``,
  simp[nag_measure_thm, hinode_size0_def] >> Cases_on `a.data` >> simp[]);

val touches_SYM' = prove(
  ``a1 : ^hinode_aty ∼ₜ a2 : ^hinode_aty ⇒ a2 ∼ₜ a1``,
  simp[touches_SYM]);

val (allnodes_rules, allnodes_ind, allnodes_cases) = Hol_reln`
  (∀a n d. nnodes a n ⇒ allnodes (a <+ d) n) ∧
  (∀a n d. allnodes d n ⇒ allnodes (a <+ d) n) ∧
  (∀a v. a.data = DN v ⇒ nnodes a <| reads := a.reads; writes := a.writes;
                                      data := v; ident := ()|>) ∧
  (∀a n g. a.data = DG g ∧ allnodes g n ⇒ nnodes a n)
`;

val allnodes_rsp = prove(
  ``wfgEQ (g1:(α,β)ndag0) g2 ⇒ allnodes g1 = allnodes g2``,
  simp[wfgEQ_def]);

val nnodes_rsp = prove(
  ``wfnEQ (n1 : ^hinode_aty) n2 ⇒ nnodes n1 = nnodes n2``,
  simp[wfnEQ_def]);

val allnodes_empty = prove(
  ``(∀(d:(α,β)ndag0) n. allnodes d n ⇒ d <> ε) ∧
    (∀(a:^hinode_aty) n. nnodes a n ⇒ T)``,
  Induct_on `allnodes` >> simp[]) |> CONJUNCT1 |> SIMP_RULE (srw_ss()) []

val allnodes_add_E = prove(
  ``(∀(d:(α,β)ndag0) n.
      allnodes d n ⇒ ∀a d0. d = a <+ d0 ⇒ nnodes a n ∨ allnodes d0 n) ∧
    (∀(a:^hinode_aty) n. nnodes a n ⇒ T)``,
  Induct_on `allnodes` >> simp[dagAdd_11_thm] >> rpt strip_tac >> rw[] >>
  metis_tac[allnodes_rules]) |> CONJUNCT1 |> SIMP_RULE (srw_ss()) [PULL_FORALL]

val allnodes_add = prove(
  ``allnodes (a <+ d) n ⇔ nnodes a n ∨ allnodes d n``,
  metis_tac[allnodes_rules, allnodes_add_E]);

val allnodes_UNION = prove(
  ``allnodes (a <+ d) = nnodes a ∪ allnodes d``,
  simp[EXTENSION, allnodes_add, SPECIFICATION]);

val allnodes_emptyset = prove(
  ``allnodes ε = ∅``,
  simp[EXTENSION, SPECIFICATION, allnodes_empty]);

val greads_def = Define`
  greads d = BIGUNION (IMAGE (λa. set a.reads) (allnodes d))
`;

val nreads_def = Define`
  nreads n = BIGUNION (IMAGE (λa. set a.reads) (nnodes n))
`;

val greads_rsp = prove(
  ``wfgEQ (g1 : (α,β)ndag0) g2 ⇒ greads g1 = greads g2``,
  simp[wfgEQ_def]);

val nreads_rsp = prove(
  ``wfnEQ (n1 : ^hinode_aty) n2 ⇒ nreads n1 = nreads n2``,
  simp[wfnEQ_def]);

val greads_thm = prove(
  ``greads ε = ∅ ∧
    greads (a <+ d) = nreads a ∪ greads d``,
  simp[nreads_def, greads_def, allnodes_emptyset, allnodes_UNION]);

val nnodes_thm = prove(
  ``nnodes (HD0 rs ws d : ^hinode_aty) =
      {<| reads := rs; writes := ws; data := d; ident := () |>} ∧
    nnodes (HG0 g : ^hinode_aty) = allnodes g``,
  conj_tac >> simp[HD0_def, HG0_def, Once allnodes_cases, FUN_EQ_THM]);

val nreads_thm = prove(
  ``nreads (HD0 rs ws d) = set rs ∧ nreads (HG0 g) = greads g``,
  simp[nnodes_thm, nreads_def, greads_def]);

val [hidagmerge_def, hidagAdd_commutes, hidagAdd_11, HG_11, HD_11, hidag_ind,
     empty_not_hidagadd, HD_not_HG, hidagAdd_11_thm, hinode_measure_thm,
     hidag_measure_thm, htouches_SYM, hnnodes_thm, hdnodes_add, hdnodes_empty, hdreads_thm,
     hnreads_thm] =
define_quotient {
  types = [{name = "hidag", equiv = wfgEQ_equiv},
           {name = "hinode", equiv = wfnEQ_equiv}],
  defs = [("emptyHDG",``emptydag : (α,β)ndag0``),
          ("hidagmerge", ``dagmerge : (α,β)ndag0 -> (α,β)ndag0 -> (α,β)ndag0``),
          ("hidagAdd", ``dagAdd : ^hinode_aty -> (α,β) ndag0 -> (α,β) ndag0``),
          ("HD", ``HD0 : β list -> β list -> α -> ((β,α)nnode,β)node``),
          ("HG", ``HG0 : (α,β)ndag0 -> ((β,α)nnode,β)node``),
          ("htouches",
           ``touches : ^hinode_aty -> ((β,α)nnode,β)node -> bool``),
          ("hinode_measure", ``hinode_size0 : ^hinode_aty -> num``),
          ("hidag_measure", ``nag_measure : (α,β)ndag0 -> num``),
          ("hdnodes", ``allnodes : (α,β)ndag0 -> (α,β)node set``),
          ("hnnodes", ``nnodes : ^hinode_aty -> (α,β)node set``),
          ("hdreads", ``greads : (α,β)ndag0 -> β set``),
          ("hnreads", ``nreads : ^hinode_aty -> β set``)
          (* ("hinodebag", ``nodebag : (α,β)ndag0 -> ((β,α)nnode,β)node bag``) *)],
  thms = [("hidagmerge_def", ndinst dagmerge_def),
          ("hidagAdd_commutes", ndinst dagAdd_commutes),
          ("hidagAdd_11[simp]", dagAdd_11'),
          ("HG_11[simp]", HG0_11),
          ("HD_11[simp]", HD0_11),
          ("hidag_ind", hidag_ind0),
          ("empty_not_hidagAdd[simp]", empty_not_hidagAdd0),
          ("HD_not_HG[simp]", HD_not_HG0),
          ("hidagAdd_11_thm", dagAdd_11_thm'),
          ("hinode_measure_thm[simp]", hinode_size0_thm),
          ("hidag_measure_thm[simp]", nag_measure_thm'),
          ("htouches_SYM", touches_SYM'),
          ("hnnodes_thm[simp]", nnodes_thm),
          ("hdnodes_add[simp]", allnodes_UNION),
          ("hdnodes_empty[simp]", allnodes_emptyset),
          ("hdreads_thm[simp]", greads_thm),
          ("hnreads_thm[simp]", nreads_thm)
          (* ("hinodebag_def", ndinst nodebag_def), *)],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfg_dagmerge, wfgEQ_emptydag, wf_dagadd, wfn_touches,
              wfnEQ_HD0, wfnEQ_HG0, nag_measure_rsp, hinode_size0_rsp,
              allnodes_rsp, nnodes_rsp, greads_rsp, nreads_rsp]}

val _ = remove_ovl_mapping "ε" {Name = "emptydag", Thy = "dag"}
val _ = overload_on("ε", ``emptyHDG``)
val _ = remove_termtok {term_name = "dagAdd", tok = "<+"}

val _ = set_mapped_fixity { fixity = Infixr 501, term_name = "hidagAdd",
                            tok = "<+" }

val (hidagR_rules, hidagR_ind, hidagR_cases) = Hol_reln`
  hidagR e af df gf ε e

    ∧

  (∀a g ar gr.
     hinodeR e af df gf a ar ∧
     hidagR e af df gf g gr
    ⇒
     hidagR e af df gf (a <+ g) (af a g ar gr))

    ∧

  (∀g gr.
     hidagR e af df gf g gr
    ⇒
     hinodeR e af df gf (HG g) (gf g gr))

    ∧

  (∀rs ws d.
     hinodeR e af df gf (HD rs ws d) (df rs ws d))
`;

val hidagR_total = prove(
  ``(∀d. ∃dr. hidagR e af df gf d dr) ∧
    (∀n. ∃nr. hinodeR e af df gf n nr)``,
  ho_match_mp_tac hidag_ind >> metis_tac[hidagR_rules]);

val hidagR_unique0 = prove(
  ``(∀n1 n2 g gr nr1 nr2.
      ¬htouches n1 n2 ⇒
      af n1 (n2 <+ g) nr1 (af n2 g nr2 gr) =
      af n2 (n1 <+ g) nr2 (af n1 g nr1 gr)) ⇒
    ∀N.
      (∀g gr1 gr2.
         hidag_measure g < N ∧
         hidagR e af df gf g gr1 ∧ hidagR e af df gf g gr2
        ⇒
         (gr2 = gr1)) ∧
      (∀n nr1 nr2.
         hinode_measure n < N ∧ hinodeR e af df gf n nr1 ∧
         hinodeR e af df gf n nr2 ⇒ (nr1 = nr2))``,
  strip_tac >> gen_tac >> completeInduct_on `N` >>
  conj_tac
  >- (qx_genl_tac [`g`, `gr1`, `gr2`] >> strip_tac >>
      Q.UNDISCH_THEN `hidagR e af df gf g gr1` mp_tac >>
      ONCE_REWRITE_TAC [hidagR_cases] >> strip_tac
      >- (rw[] >> pop_assum mp_tac >> simp[Once hidagR_cases]) >>
      qabbrev_tac `RR = hidagR e af df gf` >>
      qabbrev_tac `RN = hinodeR e af df gf` >>
      qmatch_assum_rename_tac `g = a1 <+ g1` [] >> rw[] >>
      qmatch_assum_rename_tac `RN a1 ar1` [] >>
      Q.UNDISCH_THEN `RR (a1 <+ g1) gr2` mp_tac >>
      simp[Once hidagR_cases, Abbr`RR`] >>
      simp[hidagAdd_11_thm] >> strip_tac >> rw[] >> fs[]
      >- (`hinode_measure a < hinode_measure a + hidag_measure g + 1`
            by simp[] >> metis_tac[DECIDE ``y < x + y + 1n``]) >>
      qmatch_assum_rename_tac `¬htouches a1 a2` [] >>
      qmatch_assum_rename_tac `RN a2 ar2` [] >>
      qabbrev_tac `RR = hidagR e af df gf` >>
      qmatch_assum_rename_tac `RR (a2 <+ g0) gr2` [] >>
      qmatch_assum_rename_tac `RR (a1 <+ g0) gr1` [] >>
      `∃gr0. RR g0 gr0` by metis_tac[hidagR_total] >>
      `RR (a1 <+ g0) (af a1 g0 ar1 gr0)` by metis_tac[hidagR_rules] >>
      `hidag_measure (a1 <+ g0) <
         hinode_measure a1 + (hinode_measure a2 + hidag_measure g0 + 1) + 1`
        by simp[] >>
      `gr1 = af a1 g0 ar1 gr0` by metis_tac[] >> rw[] >>
      `RR (a2 <+ g0) (af a2 g0 ar2 gr0)` by metis_tac[hidagR_rules] >>
      `hidag_measure (a2 <+ g0) <
         hinode_measure a1 + (hinode_measure a2 + hidag_measure g0 + 1) + 1`
        by simp[] >>
      `gr2 = af a2 g0 ar2 gr0` by metis_tac[] >> rw[] >>
      first_x_assum match_mp_tac >> metis_tac[htouches_SYM]) >>
  rpt strip_tac >>
  Q.UNDISCH_THEN `hinodeR e af df gf n nr1` mp_tac >>
  simp[Once hidagR_cases] >> reverse strip_tac >> rw[]
  >- (pop_assum mp_tac >> simp[Once hidagR_cases]) >>
  fs[] >>
  qpat_assum `hinodeR xx yy zz aa bb cc` mp_tac >>
  simp[Once hidagR_cases] >> rw[] >>
  `hidag_measure g < 1 + hidag_measure g` by simp[] >>
  metis_tac[])

val hidagR_unique = prove(
  ``(∀n1 n2 g gr nr1 nr2.
      ¬htouches n1 n2 ⇒
      af n1 (n2 <+ g) nr1 (af n2 g nr2 gr) =
      af n2 (n1 <+ g) nr2 (af n1 g nr1 gr)) ⇒
    (∀g gr1 gr2.
       hidagR e af df gf g gr1 ∧ hidagR e af df gf g gr2 ⇒
       gr2 = gr1) ∧
    ∀n nr1 nr2.
       hinodeR e af df gf n nr1 ∧ hinodeR e af df gf n nr2 ⇒
       nr1 = nr2``,
  metis_tac[hidagR_unique0, DECIDE ``x < x + 1n``])

val hidag_Axiom = store_thm(
  "hidag_Axiom",
  ``∀e af df gf.
     (∀n1 n2 g gr nr1 nr2.
       ¬htouches n1 n2 ⇒
       af n1 (n2 <+ g) nr1 (af n2 g nr2 gr) =
       af n2 (n1 <+ g) nr2 (af n1 g nr1 gr)) ⇒
     ∃hf nf.
       (hf ε = e) ∧
       (∀n d. hf (n <+ d) = af n d (nf n) (hf d)) ∧
       (∀rs ws d. nf (HD rs ws d) = df rs ws d) ∧
       (∀d. nf (HG d) = gf d (hf d))``,
  rpt gen_tac >> strip_tac >>
  map_every qexists_tac [
    `λd. @r. hidagR e af df gf d r`,
    `λn. @r. hinodeR e af df gf n r`] >>
  rpt strip_tac >> simp[]
  >- simp[Once hidagR_cases]
  >- (`∃nr. hinodeR e af df gf n nr` by metis_tac[hidagR_total] >>
      `∀nr'. hinodeR e af df gf n nr' ⇔ (nr' = nr)`
        by metis_tac[hidagR_unique] >> simp[] >>
      `∃dr. hidagR e af df gf d dr` by metis_tac[hidagR_total] >>
      `∀dr'. hidagR e af df gf d dr' ⇔ (dr' = dr)`
        by metis_tac[hidagR_unique] >> simp[] >>
      `hidagR e af df gf (n <+ d) (af n d nr dr)`
        by metis_tac[hidagR_rules] >>
      metis_tac[hidagR_unique])
  >- simp[Once hidagR_cases]
  >- (`∃dr. hidagR e af df gf d dr` by metis_tac[hidagR_total] >>
      `∀dr'. hidagR e af df gf d dr' ⇔ dr' = dr`
        by metis_tac[hidagR_unique] >> simp[] >>
      `hinodeR e af df gf (HG d) (gf d dr)`
        by metis_tac[hidagR_rules] >>
      metis_tac[hidagR_unique]))

val hnode_bag_def = new_specification(
  "hnode_bag_def", ["hnodebag





val _ = export_theory();
