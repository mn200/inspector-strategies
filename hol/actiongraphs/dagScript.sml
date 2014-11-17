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

val _ = overload_on("IN", ``\a d. BAG_IN a (nodebag d)``)
val _ = overload_on("nodeset", ``\d. SET_OF_BAG (nodebag d)``)

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

  ∀a1 a2. R a1.data a2.data ∧ a1.reads = a2.reads ∧ a1.write = a2.write ∧
          dagREL R d1 d2
        ⇒
          dagREL R (a1 <+ d1) (a2 <+ d2)
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
val _ = overload_on ("-", ``\d b. ITBAG ddel b d``)
val _ = overload_on ("waveset", ``λn d. SET_OF_BAG (wave n d)``)

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

val wavedepth_empty = store_thm(
  "wavedepth_empty[simp]",
  ``wavedepth ε = 0 ∧ (wavedepth d = 0 ⇔ d = ε) ∧
    (0 = wavedepth d ⇔ d = ε)``,
  conj_tac >- simp[wavedepth_def] >>
  ONCE_REWRITE_TAC [EQ_SYM_EQ] >> csimp[] >>
  simp[wavedepth_def, EQ_IMP_THM] >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[empty_wave_exists] >>
  simp[] >> simp[wave_def]);

val wavedepth_add = store_thm(
  "wavedepth_add",
  ``∀d. d ≠ ε ⇒ wavedepth d = 1 + wavedepth (ITBAG ddel (wave0 d) d)``,
  simp[wavedepth_def] >> qx_gen_tac `d` >> strip_tac >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[empty_wave_exists] >>
  qx_gen_tac `n` >> Cases_on `n = 0` >> simp[] >- simp[wave_def] >>
  `∃n0. n = SUC n0` by (Cases_on `n` >> fs[]) >> pop_assum SUBST_ALL_TAC >>
  simp[wave_def] >> strip_tac >>
  `(LEAST n. wave n (ITBAG ddel (wave0 d) d) = {||}) = n0` suffices_by simp[] >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[empty_wave_exists] >>
  qx_gen_tac `m` >> strip_tac >>
  `¬(m < n0) ∧ ¬(n0 < m)` suffices_by simp[] >> rpt strip_tac
  >- (`wave (SUC m) d ≠ {||}` by simp[] >> fs[wave_def]) >>
  metis_tac[]);

val wave0_elements_dont_touch = store_thm(
  "wave0_elements_dont_touch",
  ``∀d a b w0. wave0 d = BAG_INSERT a (BAG_INSERT b w0) ⇒ a ≁ₜ b``,
  ho_match_mp_tac dag_ind >> simp[wave0_def] >> qx_gen_tac `d` >> strip_tac >>
  map_every qx_gen_tac [`c`, `a`, `b`, `w0`] >>
  Cases_on `c = a` >> simp[]
  >- (disch_then (mp_tac o Q.AP_TERM `BAG_IN b`) >> simp[]) >>
  ONCE_REWRITE_TAC [BAG_INSERT_commutes] >>
  Cases_on `c = b` >> simp[]
  >- (disch_then (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[] >>
      metis_tac[touches_SYM]) >> strip_tac >>
  `a ≁ₜ c`
    by (pop_assum (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[] >>
        metis_tac[touches_SYM]) >>
  `b ≁ₜ c`
    by (first_x_assum (mp_tac o Q.AP_TERM `BAG_IN b`) >> simp[] >>
        metis_tac[touches_SYM]) >>
  fs[BAG_INSERT_EQUAL] >> fs[] >> rw[] >>
  first_x_assum match_mp_tac >>
  qexists_tac `wave0 d - {| a; b |}` >>
  `{| a; b |} ≤ wave0 d`
    by (`BAG_IN a (wave0 d)`
          by (first_x_assum (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[]) >>
        `∃w1. wave0 d = BAG_INSERT a w1` by metis_tac[BAG_DECOMPOSE] >>
        simp[SUB_BAG_INSERT] >>
        `c ≁ₜ b ∧ c ≁ₜ a` by metis_tac[touches_SYM] >> fs[] >>
        RULE_ASSUM_TAC (ONCE_REWRITE_RULE [BAG_INSERT_commutes]) >> fs[] >>
        first_x_assum (mp_tac o Q.AP_TERM `BAG_IN b` o
                       assert (can (find_term (same_const ``BAG_FILTER``)) o
                               concl)) >> simp[]) >>
  simp[GSYM BAG_DIFF_INSERT_SUB_BAG] >>
  simp[Once BAG_INSERT_commutes] >>
  `BAG_IN a (wave0 d)`
    by (first_x_assum (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[]) >>
  `{|a|} ≤ wave0 d` by simp[] >>
  simp[GSYM BAG_DIFF_INSERT_SUB_BAG])

val wave_elements_dont_touch = store_thm(
  "wave_elements_dont_touch",
  ``∀n d a b w0.
      wave n d = BAG_INSERT a (BAG_INSERT b w0) ⇒ a ≁ₜ b``,
  Induct >> simp[wave_def] >> metis_tac[wave0_elements_dont_touch]);

val waveset_elements_dont_touch = store_thm(
  "waveset_elements_dont_touch",
  ``∀n a b d.
       a ∈ SET_OF_BAG (wave n d) ∧ b ∈ SET_OF_BAG (wave n d) ∧ a ≠ b ⇒
       a ≁ₜ b``,
  simp[] >> rpt strip_tac >>
  `∃w1. wave n d = BAG_INSERT a w1` by metis_tac[BAG_DECOMPOSE] >>
  `BAG_IN b w1`
    by (pop_assum (mp_tac o Q.AP_TERM `BAG_IN b`) >> simp[]) >>
  `∃w2. w1 = BAG_INSERT b w2` by metis_tac [BAG_DECOMPOSE] >> rw[] >>
  metis_tac[wave_elements_dont_touch]);

val itbag_ddel_add = store_thm(
  "itbag_ddel_add",
  ``∀ms a d.
      FINITE_BAG ms ⇒
      a <+ d - ms = if BAG_IN a ms then d - (ms - {|a|})
                    else a <+ (d - ms)``,
  gen_tac >> Induct_on `BAG_CARD ms` >> rpt strip_tac
  >- (`ms = {||}` by metis_tac[BCARD_0] >> simp[]) >>
  qmatch_assum_rename_tac `SUC n = BAG_CARD ms` [] >>
  `∃ms0 b. ms = BAG_INSERT b ms0 ∧ BAG_CARD ms0 = n`
    by metis_tac[BCARD_SUC] >>
  fs[COMMUTING_ITBAG_INSERT, ddel_commutes] >>
  Cases_on `a = b` >> simp[] >>
  first_x_assum (qspec_then `ms0` mp_tac) >> simp[] >>
  simp[ddel_def, BAG_DIFF_INSERT, COMMUTING_ITBAG_INSERT, ddel_commutes,
       FINITE_BAG_DIFF]);

val wave_add = store_thm(
  "wave_add",
  ``wave n (a <+ d) = if n = 0 then BAG_INSERT a (BAG_FILTER (λb. a ≁ₜ b) (wave0 d))
                      else wave (n - 1) (d - BAG_FILTER (λb. a ≁ₜ b) (wave0 d))``,
  Cases_on `n` >> simp[wave_def, wave0_def, COMMUTING_ITBAG_INSERT, ddel_commutes,
                       FINITE_BAG_FILTER])

val dagsize_subtraction = store_thm(
  "dagsize_subtraction",
  ``b ≤ nodebag d ⇒ dagsize (d - b) = dagsize d - BAG_CARD b``,
  strip_tac >>
  `FINITE_BAG b` by metis_tac[FINITE_SUB_BAG, FINITE_nodebag] >>
  Q.UNDISCH_THEN `b ≤ nodebag d` mp_tac >> qid_spec_tac `d` >>
  pop_assum mp_tac >> qid_spec_tac `b` >>
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT >> simp[] >>
  qx_gen_tac `b` >> strip_tac >> qx_genl_tac [`e`, `d`] >>
  strip_tac >>
  simp[ddel_commutes, COMMUTING_ITBAG_INSERT, BAG_CARD_THM] >>
  imp_res_tac BAG_INSERT_SUB_BAG_E >>
  first_x_assum (qspec_then `ddel e d` mp_tac) >>
  simp[nodebag_ddel] >>
  `{|e|} ≤ nodebag d` by simp[] >>
  simp[SUB_BAG_UNION_DIFF, BAG_UNION_INSERT, IN_nodeset_ddel_size])

val IN_ddel_I = store_thm(
  "IN_ddel_I",
  ``∀d x y. x ∈ d ∧ x ≠ y ⇒ x ∈ ddel y d``,
  ho_match_mp_tac dag_ind >> dsimp[ddel_def, BAG_IN_DIFF_I]);

val IN_dagsubtract = prove(
  ``∀b. FINITE_BAG b ⇒ ∀a d:(α,β)dag. a ∈ d ∧ ¬BAG_IN a b ⇒ a ∈ d - b``,
  ho_match_mp_tac STRONG_FINITE_BAG_INDUCT >>
  simp[ddel_commutes, COMMUTING_ITBAG_INSERT] >> rpt strip_tac >>
  first_x_assum match_mp_tac >> simp[IN_ddel_I]);

val IN_dagsubtract_I = save_thm(
  "IN_dagsubtract_I",
  IN_dagsubtract |> SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO])

val waves_cover_all_nodes = store_thm(
  "waves_cover_all_nodes",
  ``∀d a. a ∈ d ⇒ ∃n. BAG_IN a (wave n d)``,
  gen_tac >> completeInduct_on `dagsize d` >> qx_gen_tac `d` >>
  strip_tac >>
  Cases_on `d = ε` >> simp[] >> qx_gen_tac `a` >> strip_tac >>
  Cases_on `BAG_IN a (wave 0 d)` >- metis_tac[] >>
  Q.REFINE_EXISTS_TAC `SUC n` >> simp[wave_def] >>
  fs[PULL_FORALL, AND_IMP_INTRO] >>
  first_x_assum match_mp_tac >>
  simp[wave_SUBBAG, dagsize_subtraction] >>
  `0 < BAG_CARD (wave0 d)`
    by (spose_not_then assume_tac >> fs[BCARD_0]) >>
  `0 < dagsize d` by (spose_not_then assume_tac >> fs[]) >>
  fs[wave_def, IN_dagsubtract_I]);

val dagmap_EQ = store_thm(
  "dagmap_EQ",
  ``∀d. (∀x. x ∈ IMAGE action_data (nodeset d) ⇒ f x = g x) ⇒
        dagmap f d = dagmap g d``,
  ho_match_mp_tac dag_ind >> dsimp[polydata_upd_def]);

val dagREL_empty = store_thm(
  "dagREL_empty[simp]",
  ``(dagREL R d ε ⇔ d = ε) ∧ (dagREL R ε d' ⇔ d' = ε)``,
  ONCE_REWRITE_TAC [dagREL_cases] >> simp[]);

val dagREL_elim_add = store_thm(
  "dagREL_elim_add",
  ``dagREL R (a <+ d1) d2 ⇔
      ∃b d0. d2 = b <+ d0 ∧ R a.data b.data ∧ dagREL R d1 d0 ∧
             b.write = a.write ∧ b.reads = a.reads``,
  reverse eq_tac >- (rw[] >> metis_tac[dagREL_rules]) >>
  `∀d1 d2. dagREL R d1 d2 ⇒
           ∀a d10. d1 = a <+ d10 ⇒
                   ∃b d20. d2 = b <+ d20 ∧ R a.data b.data ∧
                           b.write = a.write ∧ b.reads = a.reads ∧
                           dagREL R d10 d20` suffices_by metis_tac[] >>
  Induct_on `dagREL` >> simp[] >>
  qx_genl_tac [`d1`, `d2`, `a1`, `a2`] >> strip_tac >>
  qx_genl_tac [`a`, `d10`] >> simp[SimpL ``$==>``, dagAdd_11_thm] >>
  strip_tac >- (rw[] >> metis_tac[]) >>
  qmatch_assum_rename_tac `d1 = a <+ d10'` [] >>
  `∃b d20. d2 = b <+ d20 ∧ R a.data b.data ∧ b.write = a.write ∧
           b.reads = a.reads ∧ dagREL R d10' d20` by metis_tac[] >>
  rw[] >> map_every qexists_tac [`b`, `a2 <+ d20`] >> simp[] >>
  reverse conj_tac >- metis_tac[dagREL_rules] >>
  `a2 ≁ₜ b` by (fs[touches_def] >> metis_tac[]) >> simp[]);

val dagREL_O = store_thm(
  "dagREL_O",
  ``dagREL R1 O dagREL R2 RSUBSET dagREL (R1 O R2)``,
  simp[relationTheory.O_DEF, relationTheory.RSUBSET, PULL_EXISTS] >>
  ho_match_mp_tac dag_ind >> simp[] >> qx_gen_tac `d1` >> strip_tac >>
  qx_genl_tac [`a`, `d3`, `d2`] >> strip_tac >>
  Q.UNDISCH_THEN `dagREL R2 (a <+ d1) d2` mp_tac >>
  simp[dagREL_elim_add] >> rw[] >>
  qpat_assum `dagREL R1 (aa <+ dd) YY` mp_tac >> simp[dagREL_elim_add] >>
  rw[]>> simp[relationTheory.O_DEF] >> metis_tac[]);

val dagSIGMA_def = new_specification(
  "dagSIGMA_def", ["dagSIGMA"],
  dag_recursion |> ISPEC ``λa:(α,β)node b:num. b + f a.data``
                |> SPEC ``0:num``
                |> SIMP_RULE (srw_ss() ++ ARITH_ss) []
                |> GEN_ALL |> CONV_RULE SKOLEM_CONV);
val _ = export_rewrites ["dagSIGMA_def"]

val dagSIGMA_map = store_thm(
  "dagSIGMA_map[simp]",
  ``∀d. dagSIGMA f (dagmap g d) = dagSIGMA (f o g) d``,
  ho_match_mp_tac dag_ind >> simp[]);


val _ = export_theory();
