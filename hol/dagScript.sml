open HolKernel Parse boolLib bossLib;

open actionGraphTheory
open lcsymtacs boolSimps
open pairTheory pred_setTheory listTheory
open bagTheory

val _ = new_theory "dag";

val _ = type_abbrev("node", ``:(α,β,unit) action``)

val geq_def = Define`
  geq g1 g2 = ∃f. imap f g1 = g2
`;

val geq_refl = store_thm(
  "geq_refl[simp]",
  ``geq g g``,
  simp[geq_def] >> qexists_tac `λx.x` >> simp[]);

val sym_lemma = prove(
  ``INJ f (s:α set) univ(:β) ⇒
    ∃f'. INJ f' (IMAGE f s) univ(:α) ∧ ∀x. x ∈ s ⇒ f' (f x) = x``,
  strip_tac >>
  `SURJ f s (IMAGE f s)` by simp[] >>
  IMP_RES_THEN (qx_choose_then `g` strip_assume_tac) SURJ_INJ_INV >>
  qexists_tac `g` >> fs[PULL_EXISTS] >>
  conj_tac >- (match_mp_tac INJ_SUBSET >>
               map_every qexists_tac [`IMAGE f s`, `s`] >> simp[]) >>
  fs[INJ_THM] >> metis_tac[]);

val sym_lemma2 = prove(
  ``∀g f. ∃f'. imap f' (imap f g) = g``,
  rpt gen_tac >> reverse (Cases_on `INJ f (idents g) UNIV`)
  >- (simp[imap_id] >> qexists_tac `λx.x` >> simp[]) >>
  IMP_RES_THEN (qx_choose_then `f2` strip_assume_tac) sym_lemma >>
  qexists_tac `f2` >>
  `INJ (f2 o f) (idents g) UNIV` by simp[INJ_DEF] >>
  simp[imap_imap_o] >> simp[Cong imap_CONG])

val geq_sym = store_thm(
  "geq_sym",
  ``geq g1 g2 ⇔ geq g2 g1``,
  rw[geq_def, EQ_IMP_THM] >> metis_tac[sym_lemma2]);

val geq_trans = store_thm(
  "geq_trans",
  ``geq g1 g2 ∧ geq g2 g3 ⇒ geq g1 g3``,
  simp[geq_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `f1` assume_tac)
                              (qx_choose_then `f2` assume_tac)) >>
  reverse (Cases_on `INJ f1 (idents g1) UNIV`)
  >- (fs[imap_id] >> metis_tac[]) >>
  reverse (Cases_on `INJ f2 (idents g2) UNIV`)
  >- (fs[imap_id] >> metis_tac[]) >>
  `INJ f1 (idents g1) (idents g2)` by (rw[idents_imap] >> fs[INJ_THM]) >>
  `INJ (f2 o f1) (idents g1) UNIV` by metis_tac[INJ_COMPOSE] >>
  qexists_tac `f2 o f1` >> simp[GSYM imap_imap_o]);

val dagAdd0_def = Define`
  dagAdd0 (a:(α,β,unit) action) g =
    <| writes := a.writes ; reads := a.reads ;
       data := a.data; ident := LEAST n. n ∉ idents g |> ⊕ g
`;

val FINITE_idents = store_thm(
  "FINITE_idents[simp]",
  ``FINITE (idents g)``,
  simp[idents_thm]);

val idents_has_nonmembers = prove(
  ``∀g:(α,β,num) G. ∃n. n ∉ idents g``,
  metis_tac[INFINITE_NUM_UNIV, FINITE_idents, IN_INFINITE_NOT_FINITE]);

val wfdagAdd = prove(
  ``∀a g1 g2. geq g1 g2 ⇒ geq (dagAdd0 a g1) (dagAdd0 a g2)``,
  rpt gen_tac >> simp[geq_def, dagAdd0_def] >>
  disch_then (qx_choose_then `f` assume_tac) >>
  reverse (Cases_on `INJ f (idents g1) UNIV`) >> fs[imap_id]
  >- (qexists_tac `λx. x` >> simp[]) >>
  qabbrev_tac `m = LEAST n. n ∉ idents g1` >>
  qabbrev_tac `n = LEAST n. n ∉ idents g2` >>
  qabbrev_tac `f2 = λi. if i = m then n else f i` >>
  qexists_tac `f2` >>
  `m ∉ idents g1 ∧ n ∉ idents g2`
    by (conj_tac >> simp[Abbr`m`, Abbr`n`] >> numLib.LEAST_ELIM_TAC >>
        simp[idents_has_nonmembers]) >>
  `∀i. i ∈ idents g1 ⇒ i ≠ m` by metis_tac[] >>
  `∀i. i ∈ idents g1 ⇒ f i ∈ idents g2` by rw[idents_imap] >>
  `INJ f2 (m INSERT idents g1) UNIV`
    by (dsimp[INJ_DEF, Abbr`f2`] >> fs[INJ_THM] >> metis_tac[]) >>
  simp[imap_add_action] >>
  `∀i. i ∈ idents g1 ⇒ f2 i = f i` by simp[Abbr`f2`] >>
  `f2 m = n` by simp[Abbr`f2`] >>
  simp[Cong imap_CONG] >> asm_simp_tac (bool_ss ++ ETA_ss) []);

val imap_dgmap = store_thm(
  "imap_dgmap",
  ``∀G f g. imap f (dgmap g G) = dgmap g (imap f G)``,
  ho_match_mp_tac graph_ind >> simp[] >> map_every qx_gen_tac [`a`, `G`] >>
  strip_tac >> map_every qx_gen_tac [`f`, `g`] >>
  reverse (Cases_on `INJ f (a.ident INSERT idents G) UNIV`)
  >- simp[imap_id] >>
  simp[imap_add_action] >> simp[polydata_upd_def])

val wfdgmap = prove(
  ``∀f g1 g2. geq g1 g2 ⇒ geq (dgmap f g1) (dgmap f g2)``,
  rpt gen_tac >> simp[geq_def, imap_dgmap] >>
  disch_then (qx_choose_then `f2` (SUBST_ALL_TAC o SYM)) >> metis_tac[]);

val dgmap_dagAdd0 = prove(
  ``dgmap f (dagAdd0 a g) = dagAdd0 (polydata_upd f a) (dgmap f g)``,
  simp[dagAdd0_def, polydata_upd_def]);

val geq_equiv = prove(
  ``∀g1 g2. geq g1 g2 ⇔ (geq g1 = geq g2)``,
  simp[FUN_EQ_THM] >> metis_tac[geq_refl, geq_sym, geq_trans]);

val ginst = INST_TYPE [gamma |-> ``:num``]

val nullident_def = Define`
  nullident a = <| writes := a.writes; reads := a.reads; data := a.data;
                   ident := () |>
`;

val nullident_ident_upd = prove(
  ``nullident (a with ident updated_by f) = nullident a``,
  simp[nullident_def,oneTheory.one]);

val nodebag0_def = Define`
  nodebag0 G = gEVAL (BAG_INSERT o nullident) {||} G
`;

val wfnodebag = prove(
  ``∀g1 g2. geq g1 g2 ⇒ nodebag0 g1 = nodebag0 g2``,
  simp[geq_def, nodebag0_def] >> rw[] >>
  simp[gEVAL_imap_irrelevance, nullident_ident_upd,
       BAG_INSERT_commutes]);

val nodebag_emptydag0 = prove(
  ``nodebag0 (emptyG : (α,β,num) G) = {||}``,
  simp[BAG_INSERT_commutes, gEVAL_thm, nodebag0_def]);

val gE_BI = prove(
  ``gEVAL (BAG_INSERT o nullident) acc emptyG = acc ∧
    (a.ident ∉ idents g ⇒
      gEVAL (BAG_INSERT o nullident) acc (a ⊕ g) =
      gEVAL (BAG_INSERT o nullident) (BAG_INSERT (nullident a) acc) g)``,
  simp[gEVAL_thm, BAG_INSERT_commutes]);

val dagAdd_lemma = prove(
  ``∀g acc. gEVAL (BAG_INSERT o nullident) acc g =
            acc ⊎ gEVAL (BAG_INSERT o nullident) {||} g``,
  ho_match_mp_tac graph_ind >> conj_tac >- simp[] >>
  rpt strip_tac >>
  first_x_assum ((fn th => (simp[gE_BI] >> assume_tac th)) o
                 assert (is_forall o concl)) >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  simp[BAG_UNION_INSERT]);

val nodebag_dagAdd0 = prove(
  ``nodebag0 (dagAdd0 a g) = BAG_INSERT a (nodebag0 g)``,
  simp[nodebag0_def, dagAdd0_def] >>
  `(LEAST n. n ∉ idents g) ∉ idents g`
    by (numLib.LEAST_ELIM_TAC >> simp[idents_has_nonmembers]) >>
  simp[gE_BI, Once dagAdd_lemma] >> simp[BAG_UNION_INSERT] >>
  simp[nullident_def, action_component_equality, oneTheory.one]);

val nodebag_FINITE00 = prove(
  ``∀g a. FINITE_BAG a ⇒ FINITE_BAG (gEVAL (BAG_INSERT o nullident) a g)``,
  ho_match_mp_tac graph_ind >> simp[gE_BI]);

val nodebag_FINITE0 = prove(
  ``FINITE_BAG (nodebag0 g)``,
  simp[nodebag_FINITE00, nodebag0_def]);

val dagAdd_commutes0 = prove(
  ``a ≁ₜ b ⇒ geq (dagAdd0 a (dagAdd0 b g)) (dagAdd0 b (dagAdd0 a g))``,
  simp[dagAdd0_def] >>
  qabbrev_tac `m = LEAST n. n ∉ idents g` >>
  qabbrev_tac `n = LEAST n. n ≠ m ∧ n ∉ idents g` >>
  `m ∉ idents g ∧ (m ≠ n ∧ n ∉ idents g)`
    by (conj_tac >| [simp[Abbr`m`], simp[Abbr`n`]] >>
        numLib.LEAST_ELIM_TAC >> simp[] >>
        metis_tac[INFINITE_NUM_UNIV, FINITE_idents, IN_INFINITE_NOT_FINITE,
                  IN_INSERT, FINITE_INSERT]) >>
  simp[geq_def] >> strip_tac >>
  qabbrev_tac `A = λi:num. <| writes := a.writes; reads := a.reads; data := a.data;
                              ident := i |>` >>
  qabbrev_tac `B = λi:num. <| writes := b.writes; reads := b.reads; data := b.data;
                              ident := i |>` >>
  simp[] >>
  qabbrev_tac `f = λi. if i = n then m else if i = m then n else i` >>
  `f n = m ∧ f m = n ∧ ∀i. i ∈ idents g ⇒ f i = i`
    by (simp[Abbr`f`] >> metis_tac[]) >>
  `∀i h. (A i).ident = i ∧ (B i).ident = i ∧
         A i with ident updated_by h = A (h i) ∧
         B i with ident updated_by h = B (h i)` by simp[Abbr`B`, Abbr`A`] >>
  `INJ f (n INSERT m INSERT idents g) UNIV` by simp[INJ_DEF, Abbr`f`] >>
  `INJ f (m INSERT idents g) UNIV` by fs[INJ_INSERT] >>
  qexists_tac `f` >> simp[imap_add_action] >> simp[Cong imap_CONG] >>
  simp[graph_equality, add_action_edges] >> rpt strip_tac
  >- metis_tac[] >>
  `∀i j. A i ≁ₜ B j` by (simp[Abbr`A`, Abbr`B`] >> fs[touches_def]) >>
  metis_tac[touches_SYM, IN_edges])

val dag_ind0 = prove(
  ``∀P::respects (geq ===> (=)).
        P (emptyG : (α,β,num)G) ∧
        (∀a d. P d ⇒ P (dagAdd0 a d)) ⇒
        ∀d. P d``,
  simp[RES_FORALL_THM, quotientTheory.respects_def,
       quotientTheory.FUN_REL, combinTheory.W_DEF] >>
  ntac 3 strip_tac >> ho_match_mp_tac graph_ind >> simp[] >>
  map_every qx_gen_tac [`a`, `d`] >> strip_tac >>
  `geq (a ⊕ d) (dagAdd0 (nullident a) d)` suffices_by metis_tac[] >>
  simp[geq_def] >>
  qabbrev_tac `n = LEAST n. n ∉ idents d` >>
  `n ∉ idents d`
    by (simp[Abbr`n`] >>
        numLib.LEAST_ELIM_TAC >> simp[idents_has_nonmembers]) >>
  qabbrev_tac `f = λi. if i = a.ident then n else i` >>
  `INJ f (a.ident INSERT idents d) UNIV`
    by (simp[INJ_DEF,Abbr`f`] >> metis_tac[]) >>
  `∀i. i ∈ idents d ⇒ f i = i` by (simp[Abbr`f`] >> metis_tac[]) >>
  qexists_tac `f` >>
  simp[imap_add_action, Cong imap_CONG, dagAdd0_def, nullident_def] >>
  Q.ISPEC_THEN `a` strip_assume_tac action_literal_nchotomy >>
  simp[Abbr`f`])

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

val [dagmap_emptydag, dagmap_dagAdd, nodebag_emptydag, nodebag_dagAdd,
     nodebag_FINITE, dagAdd_commutes, dag_ind] =
  define_quotient {
  types = [{name = "dag", equiv = ginst geq_equiv}],
  defs = [("emptydag",``emptyG : (α,β,num)G``),
          ("dagAdd",
           ``dagAdd0 : (α,β,unit) action -> (α,β,num)G -> (α,β,num) G``),
          ("dagmap", ``dgmap : (α -> γ) -> (α,β,num) G -> (γ,β,num) G``),
          ("nodebag", ``nodebag0 : (α,β,num) G -> (α,β)node bag``)],
  thms = [("dagmap_emptydag",
           SIMP_CONV bool_ss [dgmap_emptyG]
                     ``dgmap (f : α -> γ) (emptyG : (α,β,num) G)``),
          ("dagmap_dagAdd", dgmap_dagAdd0),
          ("nodebag_emptydag", nodebag_emptydag0),
          ("nodebag_dagAdd", nodebag_dagAdd0),
          ("nodebag_FINITE", ginst nodebag_FINITE0),
          ("dagAdd_commutes", dagAdd_commutes0),
          ("dag_ind", dag_ind0)],
  poly_preserves = [],
  poly_respects = [],
  respects = [wfdgmap, wfdagAdd, wfnodebag]}

val _ = export_rewrites ["nodebag_emptydag", "nodebag_FINITE",
                         "nodebag_dagAdd", "dagmap_emptydag",
                         "dagmap_dagAdd"]

val dag_CASES = store_thm(
  "dag_CASES",
  ``∀d. d = emptydag ∨ ∃a d0. d = dagAdd a d0``,
  ho_match_mp_tac dag_ind >> simp[] >> metis_tac[]);

val dag_distinct = store_thm(
  "dag_distinct[simp]",
  ``emptydag ≠ dagAdd a d``,
  disch_then (mp_tac o Q.AP_TERM `nodebag`) >> simp[]);

val dagsize_def = Define`dagsize d = BAG_CARD (nodebag d)`

val dagsize_thm = store_thm(
  "dagsize_thm[simp]",
  ``dagsize emptydag = 0 ∧
    dagsize (dagAdd a d) = 1 + dagsize d``,
  simp[dagsize_def, BAG_CARD_THM]);

val (dagEVALR_rules, dagEVALR_ind, dagEVALR_cases) = Hol_reln`
  (∀acc. dagEVAL opn acc emptydag acc)

     ∧

  (∀a acc d r.
      dagEVAL opn (opn a acc) d r ⇒
      dagEVAL opn acc (dagAdd a d) r)
`;

val dagEVALR_total = store_thm(
  "dagEVALR_total",
  ``∀d a. ∃r. dagEVAL opn a d r``,
  ho_match_mp_tac dag_ind >> rpt strip_tac >> simp[Once dagEVALR_cases] >>
  metis_tac[]);

(*
val dagEVALR_unique = store_thm(
  "dagEVALR_unique",
  ``(∀a b acc. a ≁ₜ b ⇒ opn a (opn b acc) = opn b (opn a acc)) ⇒
    ∀a d r1.

*)
val _ = export_theory();
