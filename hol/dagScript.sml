open HolKernel Parse boolLib bossLib;

open actionGraphTheory
open lcsymtacs boolSimps
open pairTheory pred_setTheory listTheory
open bagTheory

val _ = new_theory "dag";

val _ = type_abbrev("node", ``:(α,β,unit) action``)

val (geq_rules,geq_ind,geq_cases) = Hol_reln`
  (∀g. geq g g) ∧
  (∀g1 g2. geq g1 g2 ⇒ geq g2 g1) ∧
  (∀g1 g2 g3. geq g1 g2 ∧ geq g2 g3 ⇒ geq g1 g3) ∧
  (∀a g1 g2. geq g1 g2 ⇒ geq (a::g1) (a::g2)) ∧
  (∀a:(α,β)node b:(α,β)node g. a ≁ₜ b ⇒ geq (a::b::g) (b::a::g))
`;

val geq_refl = store_thm(
  "geq_refl[simp]",
  ``geq g g``,
  simp[geq_rules]);

val geq_sym = store_thm(
  "geq_sym",
  ``geq g1 g2 ⇔ geq g2 g1``,
  metis_tac[geq_rules])

val geq_trans = store_thm(
  "geq_trans",
  ``geq g1 g2 ∧ geq g2 g3 ⇒ geq g1 g3``,
  metis_tac[geq_rules]);

val dagmap0_def = Define`
  dagmap0 f g = MAP (polydata_upd f) g
`;

val dagmap0_thm = prove(
  ``dagmap0 f [] = [] ∧
    dagmap0 f (a::g) = polydata_upd f a :: dagmap0 f g``,
  simp[dagmap0_def]);

val wfdagmap0 = prove(
  ``∀g1 g2. geq g1 g2 ⇒ geq (dagmap0 f g1) (dagmap0 f g2)``,
  Induct_on `geq` >> simp[geq_rules, dagmap0_def] >> metis_tac[geq_rules]);

val geq_equiv = prove(
  ``∀g1 g2. geq g1 g2 ⇔ (geq g1 = geq g2)``,
  simp[FUN_EQ_THM] >> metis_tac[geq_refl, geq_sym, geq_trans]);

val recursion = prove(
  ``(∀a b r. a ≁ₜ b ⇒ f a (f b r) = f b (f a r)) ⇒
    ∃h :: respects (geq ===> (=)).
      (h [] = (e:γ)) ∧
      (∀a:(α,β)node d. h (a::d) = f a (h d))``,
  simp[quotientTheory.respects_def, quotientTheory.FUN_REL,
       combinTheory.W_DEF, RES_EXISTS_THM] >> strip_tac >>
  qx_choose_then `h` strip_assume_tac
    (TypeBase.axiom_of ``:'a list``
       |> ISPEC ``e:γ``
       |> ISPEC ``λa:(α,β)node l:(α,β)node list r:γ. f a r : γ``
       |> BETA_RULE) >>
  qexists_tac `h` >> simp[] >> Induct_on `geq` >> simp[] >>
  metis_tac[]);

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

val dagAdd_commutes0 = last (CONJUNCTS geq_rules)
val wfdagAdd = List.nth(CONJUNCTS geq_rules, 3)
val alpha_node = inst [alpha |-> ``:(α,β)node``]

val [dag_ind, dag_recursion, dagAdd_commutes] =
  define_quotient {
  types = [{name = "dag", equiv = geq_equiv}],
  defs = [("emptydag",``[] : (α,β)node list``),
          ("dagAdd",
           ``CONS : (α,β) node -> (α,β) node list -> (α,β)node list``),
          ("dagmap",
           ``dagmap0 : (α -> γ) -> (α,β) node list -> (γ,β)node list``)],
  thms = [("dag_ind", TypeBase.induction_of ``:'a list``
                        |> INST_TYPE [alpha |-> ``:(α,β)node``]),
          ("dag_recursion", recursion),
          ("dagAdd_commutes", dagAdd_commutes0)],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfdagmap0, wfdagAdd]}

val _ = overload_on("ε", ``emptydag``)
val _ = set_mapped_fixity {term_name = "dagAdd", tok = "<+",
                           fixity = Infixr 501}

val dag_CASES = store_thm(
  "dag_CASES",
  ``∀d. d = emptydag ∨ ∃a d0. d = a <+ d0``,
  ho_match_mp_tac dag_ind >> simp[] >> metis_tac[]);

val nodebag_def = new_specification("nodebag_def",
  ["nodebag"],
  dag_recursion |> ISPEC (alpha_node ``BAG_INSERT``)
                |> SPEC (alpha_node ``{||}``)
                |> SIMP_RULE (srw_ss()) [BAG_INSERT_commutes]);
val _ = export_rewrites ["nodebag_def"]

val FINITE_nodebag = store_thm(
  "FINITE_nodebag[simp]",
  ``∀d. FINITE_BAG (nodebag d)``,
  ho_match_mp_tac dag_ind >> simp[]);

val nodeset_def = new_specification("nodeset_def",
  ["nodeset"],
  dag_recursion |> ISPEC (alpha_node ``(INSERT)``)
                |> SPEC (alpha_node ``∅``)
                |> SIMP_RULE (srw_ss()) [INSERT_COMM])
val _ = export_rewrites ["nodeset_def"]
val _ = overload_on("IN", ``λa d. a ∈ nodeset d``)

val FINITE_nodeset = store_thm(
  "FINITE_nodeset[simp]",
  ``∀d. FINITE (nodeset d)``,
  ho_match_mp_tac dag_ind >> simp[]);

val dagsize_def = new_specification("dagsize_def",
  ["dagsize"],
  dag_recursion |> ISPEC ``λa:(α,β)node r. r + 1`` |> SPEC ``0n``
                |> SIMP_RULE (srw_ss()) [])
val _ = export_rewrites ["dagsize_def"]

val dag_distinct = store_thm(
  "dag_distinct[simp]",
  ``emptydag ≠ dagAdd a d``,
  disch_then (mp_tac o Q.AP_TERM `dagsize`) >> simp[]);

val dagsize_EQ0 = store_thm(
  "dagsize_EQ0[simp]",
  ``(dagsize d = 0 ⇔ d = emptydag) ∧ (0 = dagsize d ⇔ d = emptydag)``,
  qspec_then `d` strip_assume_tac dag_CASES >> simp[]);

val nodebag_EQ_EMPTY = store_thm(
  "nodebag_EQ_EMPTY[simp]",
  ``(nodebag g = {||} ⇔ g = emptydag) ∧
    ({||} = nodebag g ⇔ g = emptydag)``,
  qspec_then `g` strip_assume_tac dag_CASES >> simp[]);

val dagAdd_commutes' = prove(
  ``b ≁ₜ a ⇒ a <+ b <+ g = b <+ a <+ g``,
  metis_tac[touches_SYM, dagAdd_commutes]);

val dagmap_def = new_specification("dagmap_def",
  ["dagmap"],
  dag_recursion |> ISPEC ``dagAdd o polydata_upd f`` |> SPEC ``emptydag``
                |> SIMP_RULE (srw_ss()) [dagAdd_commutes']
                |> Q.GEN `f` |> SIMP_RULE bool_ss [SKOLEM_THM]
                |> SIMP_RULE bool_ss [FORALL_AND_THM]);
val _ = export_rewrites ["dagmap_def"]

val dagmap_CONG = store_thm(
  "dagmap_CONG[defncong]",
  ``∀f1 f2 g1 g2.
      (∀d. d ∈ IMAGE action_data (nodeset g1) ⇒ f1 d = f2 d) ∧
      g1 = g2 ⇒ dagmap f1 g1 = dagmap f2 g2``,
  simp[PULL_EXISTS] >> ntac 2 gen_tac >>
  ho_match_mp_tac dag_ind >> simp[polydata_upd_def]);

val dagmerge_def = new_specification("dagmerge_def",
  ["dagmerge"],
  dag_recursion |> ISPEC ``λa:(α,β)node r g2:(α,β)dag. a <+ r g2``
                |> SPEC ``λr2:(α,β)dag. r2``
                |> SIMP_RULE (srw_ss()) [FUN_EQ_THM, dagAdd_commutes'])
val _ = export_rewrites ["dagmerge_def"]

val dagmerge_ASSOC = store_thm(
  "dagmerge_ASSOC",
  ``∀d1 d2 d3. dagmerge d1 (dagmerge d2 d3) = dagmerge (dagmerge d1 d2) d3``,
  ho_match_mp_tac dag_ind >> simp[]);

val dag_recursion' = store_thm(
  "dag_recursion'",
  ``∀f e.
      (∀a b g r. a ≁ₜ b ⇒
                 f a (b <+ g) (f b g r) = f b (a <+ g) (f a g r)) ⇒
      ∃h. h emptydag = e ∧
          ∀a d. h (a <+ d) = f a d (h d)``,
  rpt gen_tac >>
  disch_then (strip_assume_tac o
    MATCH_MP (dag_recursion
                |> ISPEC ``λa:(α,β)node r:((α,β)dag # γ).
                             (a <+ FST r, f a (FST r) (SND r) : γ)``
                |> SPEC ``(emptydag : (α,β)dag, e : γ)``
                |> SIMP_RULE (srw_ss()) [FORALL_PROD, dagAdd_commutes'])) >>
  qexists_tac `SND o h` >> simp[] >>
  `∀d. FST (h d) = d` suffices_by simp[] >>
  ho_match_mp_tac dag_ind >> simp[]);

val ddel_lemma = prove(
  ``∀b c g r.
      b ≁ₜ c ⇒
      (if a = b then c <+ g else b <+ (if a = c then g else c <+ r)) =
      (if a = c then b <+ g else c <+ (if a = b then g else b <+ r))``,
  rw[] >> simp[dagAdd_commutes']);

val ddel_def = new_specification("ddel_def",
  ["ddel"],
  MATCH_MP
    (dag_recursion'
      |> ISPEC ``λb:(α,β)node g:(α,β)dag r. if a = b then g else b <+ r``
      |> Q.SPEC `emptydag`
      |> SIMP_RULE (srw_ss()) [])
    ddel_lemma
      |> Q.GEN `a`
      |> SIMP_RULE bool_ss [SKOLEM_THM]
      |> SIMP_RULE bool_ss [FORALL_AND_THM]);

val ddel_empty = save_thm("ddel_empty[simp]", CONJUNCT1 ddel_def)

val ddel_simp = save_thm(
  "ddel_simp[simp]",
  ddel_def |> CONJUNCT2 |> SPECL [``a:(α,β)node``, ``a:(α,β)node``]
           |> REWRITE_RULE[]);

val dagAdd_11 = store_thm(
  "dagAdd_11[simp]",
  ``(a <+ g = b <+ g ⇔ a = b) ∧ (a <+ g1 = a <+ g2 ⇔ g1 = g2)``,
  simp[EQ_IMP_THM] >> conj_tac
  >- (disch_then (mp_tac o Q.AP_TERM `nodebag`) >> simp[]) >>
  disch_then (mp_tac o Q.AP_TERM `ddel a`) >> simp[]);

val (dagREL_rules, dagREL_ind, dagREL_cases) = Hol_reln`
  dagREL R ε ε ∧

  ∀a1 a2. R a1 a2 ∧ dagREL R d1 d2 ⇒ dagREL R (a1 <+ d1) (a2 <+ d2)
`

val dagREL_monotone = store_thm(
  "dagREL_monotone[mono]",
  ``(∀a b. R1 a b ⇒ R2 a b) ⇒ dagREL R1 d1 d2 ⇒ dagREL R2 d1 d2``,
  strip_tac >> map_every qid_spec_tac [`d2`, `d1`] >>
  Induct_on `dagREL` >> metis_tac[dagREL_rules]);

val dagFOLD_def = new_specification("dagFOLD_def",
  ["dagFOLD"],
  dag_recursion |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
                |> CONV_RULE (RENAME_VARS_CONV ["g"] THENC
                              STRIP_QUANT_CONV (RENAME_VARS_CONV ["f", "acc"])))

val touches_SYM' = prove(``a ∼ₜ b ⇔ b ∼ₜ a``, metis_tac[touches_SYM])

val BAG_FILTER_FILTER = prove(
  ``BAG_FILTER P (BAG_FILTER Q b) = BAG_FILTER (λa. P a ∧ Q a) b``,
  simp[BAG_FILTER_DEF] >> simp[FUN_EQ_THM] >> rw[] >> fs[]);

val wave0_def = new_specification("wave0_def",
  ["wave0"],
  dag_recursion |> ISPEC ``λa:(α,β)node b:(α,β)node bag.
                              BAG_INSERT a (BAG_FILTER (λb. a ≁ₜ b) b)``
                |> SPEC (alpha_node ``EMPTY_BAG``)
                |> SIMP_RULE (srw_ss()) []
                |> SIMP_RULE (srw_ss()) [Once touches_SYM', BAG_FILTER_FILTER]
                |> SIMP_RULE (srw_ss()) [BAG_INSERT_commutes]
                |> SIMP_RULE (srw_ss()) [Once CONJ_COMM]);

val _ = export_theory();
