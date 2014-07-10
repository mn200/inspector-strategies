open HolKernel Parse boolLib bossLib;

open actionTheory
open lcsymtacs boolSimps
open pairTheory pred_setTheory listTheory
open bagTheory
open indexedListsTheory

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

val geq_MEM = prove(
  ``∀g1 g2. geq g1 g2 ⇒ ∀a. MEM a g1 ⇔ MEM a g2``,
  Induct_on `geq` >> simp[] >> metis_tac[]);

val geq_findi = prove(
  ``∀l1 l2. geq l1 l2 ⇒
            ∀a b. a ∼ₜ b ∧ a ≠ b ∧ MEM a l1 ∧ MEM b l1 ⇒
                  (findi a l1 < findi b l1 ⇔
                   findi a l2 < findi b l2)``,
  Induct_on `geq` >> simp[] >> rpt strip_tac >> rw[findi_def] >> simp[] >>
  fs[] >> metis_tac[touches_SYM, geq_MEM])

val geq_commute_lemma = prove(
  ``geq (a::b::g1) (b::a::g2) ⇒ a = b ∨ a ≁ₜ b``,
  strip_tac >>
  qspecl_then [`a::b::g1`, `b::a::g2`] mp_tac geq_findi >> simp[] >>
  disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[findi_def] >>
  dsimp[]);

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

val [dag_ind, dag_recursion, dagAdd_commutes, dagAdd_commuteEQ_E] =
  define_quotient {
  types = [{name = "dag", equiv = geq_equiv}],
  defs = [("emptydag",``[] : (α,β)node list``),
          ("dagAdd",
           ``CONS : (α,β) node -> (α,β) node list -> (α,β)node list``)],
  thms = [("dag_ind", TypeBase.induction_of ``:'a list``
                        |> INST_TYPE [alpha |-> ``:(α,β)node``]),
          ("dag_recursion", recursion),
          ("dagAdd_commutes", dagAdd_commutes0),
          ("dagAdd_commuteEQ_E", geq_commute_lemma)],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfdagAdd]}

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

val IN_nodeset_dagsize_nonzero = store_thm(
  "IN_nodeset_dagsize_nonzero",
  ``∀dag a. a ∈ dag ⇒ 0 < dagsize dag``,
  ho_match_mp_tac dag_ind >> simp[]);

val IN_nodeset_ddel_size = store_thm(
  "IN_nodeset_ddel_size",
  ``∀dag a. a ∈ dag ⇒ dagsize (ddel a dag) = dagsize dag - 1``,
  ho_match_mp_tac dag_ind >> simp[ddel_def] >> dsimp[] >> rw[] >>
  imp_res_tac IN_nodeset_dagsize_nonzero >> simp[]);

val dagAdd_11 = store_thm(
  "dagAdd_11[simp]",
  ``(a <+ g = b <+ g ⇔ a = b) ∧ (a <+ g1 = a <+ g2 ⇔ g1 = g2)``,
  simp[EQ_IMP_THM] >> conj_tac
  >- (disch_then (mp_tac o Q.AP_TERM `nodebag`) >> simp[]) >>
  disch_then (mp_tac o Q.AP_TERM `ddel a`) >> simp[]);

val dagmap_def = new_specification("dagmap_def",
  ["dagmap"],
  dag_recursion |> ISPEC ``dagAdd o polydata_upd f`` |> SPEC ``emptydag``
                |> SIMP_RULE (srw_ss()) [dagAdd_commutes']
                |> Q.GEN `f` |> SIMP_RULE bool_ss [SKOLEM_THM]
                |> SIMP_RULE bool_ss [FORALL_AND_THM]);
val _ = export_rewrites ["dagmap_def"]

val dagmap_I = store_thm(
  "dagmap_I[simp]",
  ``dagmap I g = g ∧ dagmap (λx. x) g = g``,
  qid_spec_tac `g` >> ho_match_mp_tac dag_ind >>
  simp[polydata_upd_def, action_component_equality])

val dagmap_dagmap_o = store_thm(
  "dagmap_dagmap_o",
  ``∀d. dagmap f (dagmap g d) = dagmap (f o g) d``,
  ho_match_mp_tac dag_ind >> simp[] >>
  simp[polydata_upd_def]);

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

val wave0_empty = store_thm(
  "wave0_empty[simp]",
  ``wave0 ε = {||}``,
  simp[wave0_def]);

val BAG_FILTER_SUB_BAG = store_thm(
  "BAG_FILTER_SUB_BAG[simp]",
  ``∀P b. BAG_FILTER P b ≤ b``,
  dsimp[BAG_FILTER_DEF, SUB_BAG]);

val wave0_SUBBAG = store_thm(
  "wave0_SUBBAG[simp]",
  ``∀d. wave0 d ≤ nodebag d``,
  ho_match_mp_tac dag_ind >> simp[wave0_def, SUB_BAG_INSERT] >>
  qx_gen_tac `d` >> strip_tac >> gen_tac >>
  match_mp_tac SUB_BAG_TRANS >> qexists_tac `wave0 d` >> simp[]);

val wave0_FINITE = store_thm(
  "wave0_FINITE[simp]",
  ``FINITE_BAG (wave0 d)``,
  metis_tac[FINITE_SUB_BAG, FINITE_nodebag, wave0_SUBBAG]);

val wave0_ddel = store_thm(
  "wave0_ddel[simp]",
  ``∀d a. BAG_IN a (wave0 d) ⇒ a <+ (ddel a d) = d``,
  ho_match_mp_tac dag_ind >> simp[wave0_def] >> dsimp[] >>
  simp[ddel_def] >> rw[] >> metis_tac[dagAdd_commutes]);

val wave0_EQ_EMPTY = store_thm(
  "wave0_EQ_EMPTY[simp]",
  ``(wave0 g = {||} ⇔ g = ε) ∧ ({||} = wave0 g ⇔ g = ε)``,
  qspec_then `g` strip_assume_tac dag_CASES >> simp[wave0_def]);

val FOLDR_dagAdd_dataupd = store_thm(
  "FOLDR_dagAdd_dataupd",
  ``(∀l. FOLDR (dagAdd o polydata_upd f o g) ε l =
         dagmap f (FOLDR (dagAdd o g) ε l)) ∧
    ∀l. FOLDR (dagAdd o polydata_upd f) ε l = dagmap f (FOLDR dagAdd ε l)``,
  conj_tac >> Induct_on`l` >> simp[]);

val IN_FOLDR_dagAdd = store_thm(
  "IN_FOLDR_dagAdd[simp]",
  ``(∀l. a ∈ FOLDR (dagAdd o f) ε l ⇔ ∃e. MEM e l ∧ a = f e) ∧
    (∀l. a ∈ FOLDR dagAdd ε l ⇔ MEM a l)``,
  conj_tac >> Induct_on`l` >> simp[] >> metis_tac[]);

val EL_BAG_BAG_INSERT = store_thm(
  "EL_BAG_BAG_INSERT[simp]",
  ``{|x|} = BAG_INSERT y b ⇔ x = y ∧ b = {||}``,
  simp[EQ_IMP_THM] >>
  simp[bagTheory.BAG_EXTENSION, bagTheory.BAG_INN,
       bagTheory.BAG_INSERT, bagTheory.EMPTY_BAG] >>
  strip_tac >>
  `x = y`
    by (spose_not_then assume_tac >>
        first_x_assum (qspecl_then [`1`, `y`] mp_tac) >>
        simp[]) >> rw[] >>
  simp[EQ_IMP_THM] >> spose_not_then strip_assume_tac >> Cases_on `e = x`
  >- (rw[] >> first_x_assum (qspecl_then [`n+1`, `e`] mp_tac) >>
      simp[]) >>
  first_x_assum (qspecl_then [`n`, `e`] mp_tac) >> simp[]);

val dagAdd_commute_simp = store_thm(
  "dagAdd_commute_simp[simp]",
  ``∀g1 g2 a b. a <+ b <+ g1 = b <+ a <+ g2 ⇔ g1 = g2 ∧ (a = b ∨ a ≁ₜ b)``,
  dsimp[EQ_IMP_THM, dagAdd_commutes'] >>
  `∀g1 g2 a b. a <+ b <+ g1 = b <+ a <+ g2 ⇒ a = b ∨ a ≁ₜ b`
    suffices_by (rpt strip_tac >> res_tac >> fs[] >>
                 metis_tac[dagAdd_11, dagAdd_commutes]) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC dagAdd_commuteEQ_E);

val dagAdd_11_thm = store_thm(
  "dagAdd_11_thm",
  ``∀g1 g2 a b.
      a <+ g1 = b <+ g2 ⇔
      a = b ∧ g1 = g2 ∨
      a ≁ₜ b ∧ ∃g0. g1 = b <+ g0 ∧ g2 = a <+ g0``,
  gen_tac >> Induct_on `dagsize g1` >> simp[]
  >- (simp[EQ_IMP_THM] >> rpt gen_tac >> strip_tac >>
      first_x_assum (mp_tac o Q.AP_TERM `nodebag`) >> simp[]) >>
  qx_gen_tac `g1` >>
  qspec_then `g1` strip_assume_tac dag_CASES >> simp[] >> strip_tac >>
  qmatch_assum_rename_tac `g1 = c <+ g0` [] >>
  fs[DECIDE ``SUC m = x + 1 ⇔ m = x``] >> rpt (pop_assum SUBST_ALL_TAC) >>
  map_every qx_gen_tac [`g2`, `a`, `b`] >>
  Cases_on `a = b` >> simp[]
  >- (eq_tac >> strip_tac >> simp[]) >>
  reverse eq_tac
  >- (dsimp[PULL_EXISTS] >> simp[dagAdd_commutes']) >>
  strip_tac >>
  dsimp[PULL_EXISTS] >> Cases_on `b = c` >> simp[]
  >- (BasicProvers.VAR_EQ_TAC >>
      `g2 = a <+ g0` suffices_by (strip_tac >> fs[] >> fs[]) >>
      pop_assum (mp_tac o Q.AP_TERM `ddel b`) >> simp[ddel_def]) >>
  Cases_on `a = c` >> rw[]
  >- (first_assum (mp_tac o Q.AP_TERM `ddel a`) >> simp[ddel_def] >>
      disch_then (CONJUNCTS_THEN2 assume_tac
                                  (qx_choose_then `g00` strip_assume_tac)) >>
      rw[] >>
      `BAG_IN a (wave0 (a <+ a <+ b <+ g00))` by simp[wave0_def] >>
      `BAG_IN a (wave0 (b <+ g2))` by metis_tac[] >>
      `BAG_IN a (wave0 g2)` by (pop_assum mp_tac >> rw[wave0_def]) >>
      `a <+ a <+ g00 = a <+ ddel a g2` by simp[] >>
      simp[wave0_ddel]) >>
  first_assum (mp_tac o Q.AP_TERM `ddel c`) >> simp[ddel_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
                              (qx_choose_then `g01` strip_assume_tac)) >>
  simp[] >> conj_tac
  >- (Q.UNDISCH_THEN `a <+ c <+ g0 = b <+ g2`
                     (mp_tac o Q.AP_TERM `ddel a`) >> simp[ddel_def]) >>
  rw[] >> pop_assum kall_tac >>
  first_x_assum (mp_tac o Q.AP_TERM `ddel b`) >> simp[ddel_def])

val move_nontouching_front = prove(
  ``∀n l. n < LENGTH l ∧ (∀i. i < n ⇒ EL i l ≁ₜ EL n l) ⇒
          FOLDR dagAdd ε l = FOLDR dagAdd ε (EL n l :: delN n l)``,
  Induct >- (Cases >> simp[delN_def]) >> dsimp[LT_SUC] >>
  qx_gen_tac `l` >> strip_tac >>
  `∃h t. l = h::t` by (Cases_on `l` >> fs[]) >> rw[] >>
  simp[delN_def] >> fs[])

val BIJ_THM = store_thm(
  "BIJ_THM",
  ``BIJ f s t ⇔
       (∀x. x ∈ s ⇒ f x ∈ t) ∧
       (∀x y. x ∈ s ∧ y ∈ s ⇒ (f x = f y ⇔ x = y)) ∧
       ∀a. a ∈ t ⇒ ∃x. x ∈ s ∧ f x = a``,
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >> metis_tac[]);

val BIJ_FOLDR_add_EQ = store_thm(
  "BIJ_FOLDR_add_EQ",
  ``∀l1 l2 b.
       LENGTH l2 = LENGTH l1 ∧ BIJ b (count (LENGTH l1)) (count (LENGTH l1)) ∧
       (∀i. i < LENGTH l1 ⇒ EL (b i) l2 = EL i l1) ∧
       (∀i j. i < j ∧ j < LENGTH l1 ∧ EL i l1 ∼ₜ EL j l1 ⇒ b i < b j) ⇒
       FOLDR dagAdd ε l1 = FOLDR dagAdd ε l2``,
  Induct >> simp[] >- csimp[LENGTH_NIL] >>
  map_every qx_gen_tac [`h1`, `l2`, `b`] >>
  strip_tac >>
  qmatch_assum_rename_tac `LENGTH l2 = SUC (LENGTH t1)` [] >>
  `EL 0 (h1::t1) = h1` by simp[] >>
  `EL (b 0) l2 = h1` by simp[] >>
  `b 0 < SUC (LENGTH t1)`
    by metis_tac[BIJ_DEF, SURJ_DEF, IN_COUNT, DECIDE ``0 < SUC x``] >>
  `∀j. j < b 0 ⇒ EL j l2 ≁ₜ h1`
    by (spose_not_then strip_assume_tac >>
        `j < SUC (LENGTH t1)` by simp[] >>
        `∃i. i < SUC (LENGTH t1) ∧ b i = j` by fs[BIJ_DEF, SURJ_DEF] >>
        `¬(b 0 < b i)` by simp[] >>
        `i ≠ 0` by (strip_tac >> fs[]) >>
        `0 < i` by simp[] >>
        metis_tac[touches_SYM]) >>
  `FOLDR dagAdd ε l2 = FOLDR dagAdd ε (EL (b 0) l2 :: delN (b 0) l2)`
    by simp[move_nontouching_front] >>
  pop_assum SUBST_ALL_TAC >> simp[] >> first_x_assum match_mp_tac >>
  simp[delN_shortens] >>
  qabbrev_tac `b' = λi. if b 0 < b (i + 1) then b (i + 1) - 1
                        else b (i + 1)` >>
  `BIJ b' (count (LENGTH t1)) (count (LENGTH t1))`
    by (fs[Abbr`b'`, BIJ_THM] >> rpt strip_tac
        >- (`i + 1 < SUC (LENGTH t1)` by simp[] >>
            `b(i + 1) < SUC (LENGTH t1)` by simp[] >>
            COND_CASES_TAC >- simp[] >>
            `b (i + 1) ≠ b 0` by simp[] >>
            simp[])
        >- (pop_assum mp_tac >>
            qmatch_assum_rename_tac `m < LENGTH t1` [] >>
            strip_tac >>
            qmatch_assum_rename_tac `n < LENGTH t1` [] >>
            Cases_on `b 0 < b (m + 1)` >> simp[]
            >- (Cases_on `b 0 < b (n + 1)` >> simp[]
                >- simp[DECIDE ``0 < y ∧ 0 < z ⇒ (y - 1n = z - 1 ⇔ y = z)``] >>
                `b 0 ≠ b (n + 1)`
                  by (`0 < SUC (LENGTH t1) ∧ n + 1 < SUC (LENGTH t1)`
                        by simp[] >>
                      simp[]) >>
                `b (m + 1) - 1 ≠ b (n + 1)` by simp[] >> simp[] >>
                strip_tac >> fs[]) >>
            Cases_on `b 0 < b (n + 1)` >> simp[]
            >- (`b 0 ≠ b (m + 1)`
                  by (`0 < SUC (LENGTH t1) ∧ m + 1 < SUC (LENGTH t1)`
                        by simp[] >>
                      simp[]) >>
                `b (m + 1) ≠ b (n + 1) - 1` by simp[] >> simp[] >>
                strip_tac >> fs[]))
        >- (Cases_on `a < b 0`
            >- (`a < SUC (LENGTH t1)` by simp[] >>
                `∃x. x < SUC (LENGTH t1) ∧ b x = a` by metis_tac[] >>
                `x ≠ 0` by (strip_tac >> fs[]) >>
                qexists_tac `x - 1` >> simp[]) >>
            `a + 1 < SUC (LENGTH t1)` by simp[] >>
            `∃x. x < SUC (LENGTH t1) ∧ b x = a + 1` by metis_tac[] >>
            `x ≠ 0` by (strip_tac >> fs[]) >>
            qexists_tac `x - 1` >> simp[])) >>
  qexists_tac `b'` >> simp[] >> conj_tac
  >- (simp[Abbr`b'`] >> qx_gen_tac `i` >> strip_tac >>
      `i + 1 < SUC (LENGTH t1)` by simp[] >>
      Cases_on `b 0 < b (i + 1)` >> simp[]
      >- (`b (i + 1) < SUC (LENGTH t1)` by fs[BIJ_THM] >>
          simp[EL_delN_AFTER] >>
          simp[GSYM arithmeticTheory.ADD1]) >>
      `b (i + 1) ≠ b 0` by fs[BIJ_THM] >>
      `b (i + 1) < b 0` by simp[] >>
      simp[EL_delN_BEFORE] >>
      simp[GSYM arithmeticTheory.ADD1]) >>
  map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
  simp[Abbr`b'`] >>
  Cases_on `b 0 < b (i + 1)` >> simp[]
  >- (Cases_on `b 0 < b (j + 1)` >> simp[]
      >- (`b (i + 1) < b (j + 1)` suffices_by simp[] >>
          first_x_assum match_mp_tac >>
          simp[GSYM arithmeticTheory.ADD1]) >>
      `b (j + 1) ≠ b 0` by (fs[BIJ_THM] >> simp[]) >>
      `b (j + 1) < b (i + 1)` by simp[] >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
      simp[] >> simp[arithmeticTheory.ADD1]) >>
  `b (i + 1) ≠ b 0` by (fs[BIJ_THM] >> simp[]) >>
  Cases_on `b 0 < b (j + 1)` >> simp[] >>
  first_x_assum match_mp_tac >> simp[GSYM arithmeticTheory.ADD1])

val dagmerge_EQ_empty = store_thm(
  "dagmerge_EQ_empty[simp]",
  ``dagmerge g1 g2 = ε ⇔ g1 = ε ∧ g2 = ε``,
  map_every qid_spec_tac [`g2`, `g1`] >> ho_match_mp_tac dag_ind >> simp[]);

val dagAdd_EQ_sing = store_thm(
  "dagAdd_EQ_sing[simp]",
  ``a <+ g = b <+ ε ⇔ a = b ∧ g = ε``,
  map_every qid_spec_tac [`a`, `b`, `g`] >> ho_match_mp_tac dag_ind >> simp[] >>
  rpt strip_tac >> first_x_assum (mp_tac o Q.AP_TERM `dagsize`) >> simp[]);

val dagmerge_EQ_sing = store_thm(
  "dagmerge_EQ_sing",
  ``dagmerge g1 g2 = a <+ ε ⇔ g1 = a <+ ε ∧ g2 = ε ∨ g1 = ε ∧ g2 = a <+ ε``,
  map_every qid_spec_tac [`a`, `g2`, `g1`] >> ho_match_mp_tac dag_ind >>
  simp[] >> metis_tac[]);

val ddel_commutes = store_thm(
  "ddel_commutes",
  ``∀g a b. (* a ≁ₜ b ⇒ *) ddel a (ddel b g) = ddel b (ddel a g)``,
  ho_match_mp_tac dag_ind >> simp[ddel_def] >> rw[] >> rw[] >>
  simp[ddel_def] >> first_x_assum match_mp_tac >> simp[]);

val wave_def = Define`
  wave 0 g = wave0 g ∧
  wave (SUC n) g = wave n (ITBAG ddel (wave0 g) g)
`;

val wave_empty = store_thm(
  "wave_empty[simp]",
  ``wave n ε = {||}``,
  Induct_on `n` >> simp[wave_def]);

val nodebag_ddel = store_thm(
  "nodebag_ddel[simp]",
  ``∀d a. nodebag (ddel a d) = nodebag d - {|a|}``,
  ho_match_mp_tac dag_ind >> simp[ddel_def] >> qx_gen_tac `d` >> strip_tac >>
  map_every qx_gen_tac [`h`, `a`] >> COND_CASES_TAC >> simp[BAG_DIFF_INSERT]);

val nodebag_ITBAG_ddel = store_thm(
  "nodebag_ITBAG_ddel",
  ``∀b. FINITE_BAG b ⇒ nodebag (ITBAG ddel b d) = nodebag d - b``,
  Induct_on `FINITE_BAG` >>
  simp[COMMUTING_ITBAG_RECURSES, ddel_commutes, BAG_DIFF_2L, BAG_UNION_INSERT]);

val wave_SUBBAG = store_thm(
  "wave_SUBBAG",
  ``∀n d. wave n d ≤ nodebag d``,
  Induct >> simp[wave_def] >> qx_gen_tac `d` >>
  first_x_assum (qspec_then `ITBAG ddel (wave0 d) d` mp_tac) >>
  `nodebag (ITBAG ddel (wave0 d) d) ≤ nodebag d` suffices_by
    metis_tac[SUB_BAG_TRANS] >>
  simp[nodebag_ITBAG_ddel]);

val dagsize_CARD_nodebag = store_thm(
  "dagsize_CARD_nodebag",
  ``∀d. dagsize d = BAG_CARD (nodebag d)``,
  ho_match_mp_tac dag_ind >> simp[BAG_CARD_THM]);

val BAG_CARD_DIFF = store_thm(
  "BAG_CARD_DIFF",
  ``∀b. FINITE_BAG b ⇒
        ∀c. c ≤ b ⇒ BAG_CARD (b - c) = BAG_CARD b - BAG_CARD c``,
  Induct_on `FINITE_BAG` >> simp[BAG_CARD_THM] >> qx_gen_tac `b` >> strip_tac >>
  map_every qx_gen_tac [`e`, `c`] >> strip_tac >>
  `FINITE_BAG c` by metis_tac[FINITE_BAG_THM, FINITE_SUB_BAG] >>
  Cases_on `BAG_IN e c`
  >- (`∃c0. c = BAG_INSERT e c0` by metis_tac[BAG_DECOMPOSE] >>
      lfs[BAG_CARD_THM, SUB_BAG_INSERT]) >>
  simp[BAG_DIFF_INSERT, BAG_CARD_THM, FINITE_BAG_DIFF] >>
  lfs[NOT_IN_SUB_BAG_INSERT] >>
  `BAG_CARD c ≤ BAG_CARD b` by simp[SUB_BAG_CARD] >> simp[]);

val empty_wave_exists = store_thm(
  "empty_wave_exists",
  ``∀d. ∃n. wave n d = {||}``,
  gen_tac >> completeInduct_on `dagsize d` >>
  qx_gen_tac `d` >> strip_tac >>
  Cases_on `wave0 d = {||}` >> fs[] >>
  Q.REFINE_EXISTS_TAC `SUC m` >> simp[wave_def] >>
  fs[PULL_FORALL] >> first_x_assum match_mp_tac >>
  `∀b. FINITE_BAG b ⇒
       ∀d. b ≤ nodebag d ⇒ dagsize (ITBAG ddel b d) = dagsize d - BAG_CARD b`
    suffices_by
      (disch_then (qspec_then `wave0 d` mp_tac) >> simp[] >>
       disch_then (qspec_then `d` mp_tac) >> simp[] >> strip_tac >>
       qspec_then `d` strip_assume_tac dag_CASES >>
       simp[wave0_def, FINITE_BAG_FILTER, BAG_CARD_THM]) >>
  rpt (pop_assum kall_tac) >> Induct_on `FINITE_BAG` >>
  simp[COMMUTING_ITBAG_RECURSES, ddel_commutes] >>
  simp[dagsize_CARD_nodebag, nodebag_ITBAG_ddel,
       GSYM BAG_CARD_DIFF, BAG_DIFF_2L, BAG_UNION_INSERT]);

val wavedepth_def = Define`
  wavedepth g = LEAST n. wave n g = {||}
`;

val LEAST_T = store_thm(
  "LEAST_T[simp]",
  ``(LEAST n. T) = 0``,
  numLib.LEAST_ELIM_TAC >> simp[] >>
  spose_not_then strip_assume_tac >> first_x_assum (qspec_then `0` mp_tac) >>
  simp[]);

val wavedepth_empty = store_thm(
  "wavedepth_empty[simp]",
  ``wavedepth ε = 0 ∧ (wavedepth d = 0 ⇔ d = ε) ∧
    (0 = wavedepth d ⇔ d = ε)``,
  conj_tac >- simp[wavedepth_def] >>
  ONCE_REWRITE_TAC [EQ_SYM_EQ] >> csimp[] >>
  simp[wavedepth_def, EQ_IMP_THM] >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[empty_wave_exists] >>
  simp[] >> simp[wave_def]);

val _ = export_theory();
