open HolKernel Parse boolLib bossLib;

open lcsymtacs boolSimps
open pred_setTheory listTheory pairTheory optionTheory
open monadsyntax

open nagTheory
open PseudoCTheory
open PseudoCPropsTheory
open actionGraphTheory
open indexedListsTheory

val _ = new_theory "PseudoCNAG";

val (nagER_rules,nagER_ind,nagER_cases) = Hol_reln`
  (∀m.
      nagER m emptyG m)

      ∧

  (∀a g d m0 m.
      a.ident ∉ idents g ∧
      a.data = DN d ∧
      nagER (apply_action (polydata_upd (K d) a) m0) g m
     ⇒
      nagER m0 (a ⊕ g) m)

      ∧

  (∀a g g0 m0 m' m.
      a.ident ∉ idents g ∧
      a.data = DG g0 ∧
      nagER m0 g0 m' ∧
      nagER m' g m
     ⇒
      nagER m0 (a ⊕ g) m)
`;

val gwrites_def = Define`
  gwrites g = BIGUNION (IMAGE (λa. set a.writes) (ag_nodes g))
`;

val gwrites_thm = store_thm(
  "gwrites_thm[simp]",
  ``gwrites emptyG = ∅ ∧
    (a.ident ∉ idents g ⇒ gwrites (a ⊕ g) = set a.writes ∪ gwrites g)``,
  simp[gwrites_def] >> dsimp[Once EXTENSION]);

val greads_def = Define`
  greads g = BIGUNION (IMAGE (λa. set a.reads) (ag_nodes g))
`;

val greads_thm = store_thm(
  "greads_thm[simp]",
  ``greads emptyG = ∅ ∧
    (a.ident ∉ idents g ⇒ greads (a ⊕ g) = set a.reads ∪ greads g)``,
  simp[greads_def] >> dsimp[Once EXTENSION]);


val (wfnag_rules, wfnag_ind, wfnag_cases) = Hol_reln`
  (∀g. (∀a g0. a ∈ g ∧ a.data = DG g0 ⇒
               wfnag g0 ∧
               set a.writes = gwrites g0 ∧
               set a.reads = greads g0) ⇒
       wfnag g)
`;

val wfnnode_def = Define`
  wfnnode a =
    case a.data of DN _ => T
                 | DG g => wfnag g ∧ set a.writes = gwrites g ∧
                           set a.reads = greads g
`

val graph_CASES = store_thm(
  "graph_CASES",
  ``∀g. g = emptyG ∨ ∃a g0. a.ident ∉ idents g0 ∧ g = a ⊕ g0``,
  ho_match_mp_tac graph_ind >> simp[] >> metis_tac[]);

val nagER_total = store_thm(
  "nagER_total",
  ``∀g m0. ∃m. nagER m0 g m``,
  gen_tac >> completeInduct_on `nagSize g` >>
  gen_tac >> fs[PULL_FORALL] >>
  Q.ISPEC_THEN `g` strip_assume_tac graph_CASES
  >- simp[Once nagER_cases] >>
  simp[] >> gen_tac >> rw[] >>
  Cases_on `a.data`
  >- (first_x_assum (qspecl_then [`g0`, `apply_action (polydata_upd (K d) a) m0`]
                                 mp_tac) >> simp[] >>
      metis_tac[nagER_rules]) >>
  first_assum (qspecl_then [`g`,`m0`]
                           (mp_tac o SIMP_RULE (srw_ss() ++ ARITH_ss) [])) >>
  disch_then (qx_choose_then `m'` assume_tac) >>
  first_x_assum (qspecl_then [`g0`, `m'`] mp_tac) >> simp[] >>
  metis_tac[nagER_rules]);

val wfnag_empty = store_thm(
  "wfnag_empty[simp]",
  ``wfnag emptyG``,
  simp[Once wfnag_cases])

val wfnag_add_action = store_thm(
  "wfnag_add_action",
  ``a.ident ∉ idents g ⇒ (wfnag (a ⊕ g) ⇔ wfnag g ∧ wfnnode a)``,
  simp[wfnnode_def] >> simp[Once wfnag_cases, SimpLHS] >> dsimp[] >>
  simp[Once wfnag_cases, SimpRHS, SimpL ``$/\``] >>
  Cases_on `a.data` >> dsimp[] >> metis_tac[]);

val nagER_empty = store_thm(
  "nagER_empty[simp]",
  ``nagER m0 emptyG m ⇔ m = m0``,
  simp[Once nagER_cases]);

val gtouches_lemma = prove(
  ``adata a = DG g ∧ gwrites g = set a.writes ∧ greads g = set a.reads ∧
    a ≁ₜ b ⇒ ∀c. c ∈ g ⇒ c ≁ₜ b``,
  simp[touches_def] >> simp[GSYM IMP_DISJ_THM] >> strip_tac >> gen_tac >>
  strip_tac >>
  `(∀w. MEM w c.writes ⇒ MEM w a.writes) ∧
   (∀w. MEM w c.reads ⇒ MEM w a.reads)`
    by (fs[gwrites_def, greads_def] >>
        rpt (qpat_assum `BIGUNION xx = yy` (mp_tac o SYM)) >>
        dsimp[] >> metis_tac[]) >>
  metis_tac[]);

val gtouches_lemma2 = prove(
  ``adata a = DG g1 ∧ gwrites g1 = set a.writes ∧ greads g1 = set a.reads ∧
    (∀b. b ∈ g2 ⇒ a ≁ₜ b) ⇒ ¬gtouches g1 g2``,
  simp[gtouches_def, touches_def, GSYM IMP_DISJ_THM] >> strip_tac >>
  map_every qx_gen_tac [`a1`, `a2`] >> ntac 2 strip_tac >>
  `(∀w. MEM w a1.writes ⇒ MEM w a.writes) ∧
   (∀w. MEM w a1.reads ⇒ MEM w a.reads)` suffices_by metis_tac[] >>
  fs[gwrites_def, greads_def] >>
  rpt (qpat_assum `BIGUNION xx = y` (SUBST1_TAC o SYM)) >>
  dsimp[] >> metis_tac[]);

val gtouches_lemma3 = prove(
  ``gwrites g01 = set a1.writes ∧ greads g01 = set a1.reads ∧
    gwrites g02 = set a2.writes ∧ greads g02 = set a2.reads ∧
    a1 ≁ₜ a2 ⇒ ¬gtouches g01 g02``,
  simp[gtouches_def, touches_def, GSYM IMP_DISJ_THM] >> strip_tac >>
  map_every qx_gen_tac [`b`, `c`] >> ntac 2 strip_tac >>
  `(∀w. MEM w b.writes ⇒ MEM w a1.writes) ∧
   (∀w. MEM w b.reads ⇒ MEM w a1.reads) ∧
   (∀w. MEM w c.writes ⇒ MEM w a2.writes) ∧
   (∀w. MEM w c.reads ⇒ MEM w a2.reads)` suffices_by metis_tac[] >>
  fs[gwrites_def, greads_def] >>
  rpt (qpat_assum `BIGUNION xx = y` (SUBST1_TAC o SYM)) >>
  dsimp[] >> metis_tac[]);

val apply_action_nagER_commutes = store_thm(
  "apply_action_nagER_commutes",
  ``∀ma g:(value list -> value,α,actionRW)nag0 m.
       nagER ma g m ⇒
       wfnag g ⇒
       ∀a:(value list -> value,actionRW,α)action m0.
              ma = apply_action a m0 ∧ (∀b. b ∈ g ⇒ b ≁ₜ a) ⇒
              ∃m'. nagER m0 g m' ∧ m = apply_action a m'``,
  Induct_on `nagER` >> simp[] >> rpt conj_tac
  >- (map_every qx_gen_tac [`a`, `g`, `d`, `ma`, `m`] >>
      csimp[wfnag_add_action,wfnnode_def] >> ntac 2 strip_tac >> fs[] >>
      map_every qx_gen_tac [`b`, `m0`] >> dsimp[] >> strip_tac >>
      qabbrev_tac `a' = polydata_upd (K d) a` >> rw[] >>
      `a' ≁ₜ b` by simp[Abbr`a'`, polydata_upd_def] >>
      first_x_assum (qspecl_then [`b`, `apply_action a' m0`] mp_tac) >>
      simp[apply_action_commutes] >>
      disch_then (qx_choose_then `m'` strip_assume_tac) >>
      qexists_tac `m'` >> simp[] >>
      match_mp_tac (List.nth(CONJUNCTS nagER_rules, 1)) >>
      simp[]) >>
  map_every qx_gen_tac [`a`, `g`, `g0`, `ma`, `m1`, `m`] >>
  simp[wfnag_add_action,wfnnode_def] >> ntac 2 strip_tac >>
  map_every qx_gen_tac [`b`, `m0`] >> dsimp[] >> strip_tac >> rw[] >>
  `∀b'. b' ∈ g0 ⇒ b' ≁ₜ b` by metis_tac[gtouches_lemma] >> fs[] >>
  `∃m'. nagER m0 g0 m' ∧ m1 = apply_action b m'` by metis_tac[] >> rw[] >>
  `∃m''. nagER m' g m'' ∧ m = apply_action b m''` by metis_tac[] >> rw[] >>
  qexists_tac `m''` >> simp[] >> match_mp_tac (last (CONJUNCTS nagER_rules)) >>
  metis_tac[]);

val nagER_commutes = store_thm(
  "nagER_commutes",
  ``∀m0 g1 m1. nagER m0 g1 m1 ⇒
               wfnag g1 ⇒
               ∀g2 m2. wfnag g2 ∧ ¬gtouches g1 g2 ∧ nagER m1 g2 m2 ⇒
                       ∃m1'. nagER m0 g2 m1' ∧ nagER m1' g1 m2``,
  Induct_on `nagER` >> simp[] >> rpt conj_tac
  >- (map_every qx_gen_tac [`a`, `g1`, `d`, `m0`, `m1`] >>
      dsimp[wfnag_add_action, GSYM IMP_DISJ_THM] >>
      map_every qx_gen_tac [`g2`, `m2`] >> rpt strip_tac >> fs[] >>
      qabbrev_tac `a' = polydata_upd (K d) a` >>
      `∃m'. nagER (apply_action a' m0) g2 m' ∧ nagER m' g1 m2` by metis_tac[] >>
      `∀b. b ∈ g2 ⇒ b ≁ₜ a'` by (simp[Abbr`a'`] >> metis_tac[touches_SYM]) >>
      `∃m0'. nagER m0 g2 m0' ∧ m' = apply_action a' m0'`
        by metis_tac[apply_action_nagER_commutes] >>
      rw[] >> qexists_tac `m0'` >> simp[] >>
      match_mp_tac (List.nth(CONJUNCTS nagER_rules, 1)) >> simp[]) >>
  map_every qx_gen_tac [`a`, `g1`, `g10`, `m0`, `m0'`, `m1`] >>
  simp[wfnag_add_action,wfnnode_def] >> ntac 2 strip_tac >> fs[GSYM IMP_DISJ_THM] >>
  map_every qx_gen_tac [`g2`, `m2`] >> strip_tac >>
  `∃m1'. nagER m0' g2 m1' ∧ nagER m1' g1 m2` by metis_tac[] >>
  `¬gtouches g10 g2` by metis_tac[gtouches_lemma2] >>
  `∃m00. nagER m0 g2 m00 ∧ nagER m00 g10 m1'` by metis_tac[] >>
  qexists_tac `m00` >> simp[] >>
  match_mp_tac (last (CONJUNCTS nagER_rules)) >> simp[] >>
  metis_tac[]);

val gDELETE_add_action = store_thm(
  "gDELETE_add_action",
  ``a.ident ∉ idents g ⇒ (a ⊕ g) \\ a = g``,
  dsimp[graph_equality, add_action_edges, EQ_IMP_THM] >>
  dsimp[idents_thm, GSYM IMP_DISJ_THM] >>
  metis_tac[IN_edges]);

val NOTIN_idents_gDELETE = store_thm(
  "NOTIN_idents_gDELETE",
  ``i ∉ idents g ⇒ i ∉ idents (g \\ a)``,
  simp[idents_thm] >> metis_tac[]);

val add_action_11 = store_thm(
  "add_action_11[simp]",
  ``(a.ident ∉ idents g1 ∧ a.ident ∉ idents g2 ⇒
     (a ⊕ g1 = a ⊕ g2 ⇔ g1 = g2)) ∧
    (a1.ident ∉ idents g ∧ a2.ident ∉ idents g ⇒
     (a1 ⊕ g = a2 ⊕ g ⇔ a1 = a2))``,
  simp[EQ_IMP_THM] >> conj_tac
  >- (strip_tac >> disch_then (mp_tac o Q.AP_TERM `λg. g \\ a`) >>
      simp[gDELETE_add_action]) >>
  strip_tac >> disch_then (mp_tac o Q.AP_TERM `λg. a1 ∈ g`) >>
  simp[] >> fs[idents_thm] >> metis_tac[]);

val add_action_commutes = store_thm(
  "add_action_commutes",
  ``a1 ≁ₜ a2 ∧ a1.ident ≠ a2.ident ∧ a1.ident ∉ idents g ∧ a2.ident ∉ idents g ⇒
    a1 ⊕ (a2 ⊕ g) = a2 ⊕ (a1 ⊕ g)``,
  simp[graph_equality, add_action_edges] >> rpt strip_tac
  >- metis_tac[] >> eq_tac >> strip_tac >> rw[] >> fs[] >>
  metis_tac[touches_SYM]);

val double_graph_decomposition = store_thm(
  "double_graph_decomposition",
  ``a1 ⊕ g1 = a2 ⊕ g2 ∧ a1 ≠ a2 ∧ a1.ident ∉ idents g1 ∧ a2.ident ∉ idents g2 ⇒
    a1 ≁ₜ a2 ∧
    ∃g0. g1 = a2 ⊕ g0 ∧ g2 = a1 ⊕ g0 ∧
         a1.ident ∉ idents g0 ∧ a2.ident ∉ idents g0``,
  strip_tac >>
  `a2 ∈ g1 ∧ a1 ∈ g2` by metis_tac[IN_add_action] >>
  `a1 ∉ g1 ∧ a2 ∉ g2 ∧ a1.ident ∈ idents g2 ∧ a2.ident ∈ idents g1`
    by (fs[idents_thm] >> metis_tac[]) >>
  `g1 \\ a2 = g2 \\ a1`
    by (simp[graph_equality] >> conj_tac
        >- (first_assum (mp_tac o Q.AP_TERM `ag_nodes`) >>
            simp_tac (srw_ss()) [EXTENSION] >> simp[] >> metis_tac[]) >>
        metis_tac[IN_edges, add_action_edges]) >>
  qabbrev_tac `g00 = g1 \\ a2` >>
  `∀b. b -<a1 ⊕ g1>/-> a2`
    by (simp[] >> simp[add_action_edges] >> metis_tac[IN_edges]) >>
  pop_assum mp_tac >> simp[add_action_edges, FORALL_AND_THM] >>
  strip_tac >>
  `a2.ident ∉ idents g00` by simp[Abbr`g00`, NOTIN_idents_gDELETE] >>
  `a1.ident ∉ idents g00` by simp[Abbr`g00`, NOTIN_idents_gDELETE] >>
          `a1.ident ≠ a2.ident` by metis_tac[] >>
  `g1 = a2 ⊕ g00`
    by (qunabbrev_tac `g00` >>
        simp[graph_equality, gDELETE_edges, add_action_edges,
             NOTIN_idents_gDELETE] >> conj_tac >- metis_tac[] >>
        metis_tac[touching_actions_link, IN_edges]) >>
  `g2 = a1 ⊕ g00`
    by (`a1 ⊕ (a2 ⊕ g00) = a2 ⊕ (a1 ⊕ g00)`
          by metis_tac[add_action_commutes, touches_SYM] >>
        Q.UNDISCH_THEN `g1 = a2 ⊕ g00` SUBST_ALL_TAC >>
        pop_assum SUBST_ALL_TAC >>
        Q.UNDISCH_THEN `a1.ident ≠ a2.ident` assume_tac >>
        fs[add_action_11, idents_add_action, NOTIN_idents_gDELETE]) >>
  qexists_tac `g00` >> metis_tac[]);

val action_graph_case = prove(
  ``(∀g':(value list->value,α,actionRW)nag0 m0 m1 m2.
       nagSize g' < nagSize g ⇒
       wfnag g' ∧ nagER m0 g' m1 ∧ nagER m0 g' m2 ⇒ m1 = m2) ∧
    wfnag (g:(value list->value,α,actionRW)nag0) ∧
    g = a1 ⊕ g1 ∧ a1 ⊕ g1 = a2 ⊕ g2 ∧
    a1.ident ∉ idents g1 ∧ a2.ident ∉ idents g2 ∧
    adata a1 = DG g0 ∧ nagER m0 g0 m00 ∧ nagER m00 g1 m1 ∧
    adata a2 = DN d ∧
    nagER (apply_action (polydata_upd (K d) a2) m0) g2 m2 ⇒
    m1 = m2``,
  strip_tac >>
  `a1 ≠ a2` by (strip_tac >> fs[]) >>
  `∃g00. g1 = a2 ⊕ g00 ∧ g2 = a1 ⊕ g00 ∧
         a1 ≁ₜ a2 ∧ a1.ident ∉ idents g00 ∧
         a2.ident ∉ idents g00`
    by metis_tac[double_graph_decomposition] >>
  rw[] >>
  qabbrev_tac `a2' = polydata_upd (K d) a2` >>
  `∃mm01 mm. nagER (apply_action a2' m0) g0 mm01 ∧
             nagER mm01 g00 mm`
    by metis_tac [nagER_total] >>
  `nagER (apply_action a2' m0) (a1 ⊕ g00) mm`
    by (match_mp_tac (last (CONJUNCTS nagER_rules)) >>
        simp[] >> metis_tac[]) >>
  `nagSize (a1 ⊕ g00) < nagSize (a1 ⊕ (a2 ⊕ g00))` by simp[] >>
  `wfnag (a1 ⊕ g00)` by fs[wfnag_add_action,wfnnode_def] >>
  `m2 = mm` by metis_tac[] >>
  pop_assum SUBST_ALL_TAC >>
  `∀b. b ∈ g0 ⇒ b ≁ₜ a2'`
    by (simp[Abbr`a2'`] >> fs[wfnag_add_action,wfnnode_def] >>
        metis_tac[gtouches_lemma, touches_SYM]) >>
  `wfnag g0` by fs[wfnag_add_action,wfnnode_def] >>
  `∃mm02. nagER m0 g0 mm02 ∧ mm01 = apply_action a2' mm02`
    by metis_tac[apply_action_nagER_commutes] >>
  pop_assum SUBST_ALL_TAC >>
  `nagSize g0 < nagSize (a1 ⊕ (a2 ⊕ g00))` by simp[] >>
  `m00 = mm02` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
  `nagER mm02 (a2 ⊕ g00) mm`
    by (match_mp_tac (List.nth(CONJUNCTS nagER_rules, 1)) >>
        simp[]) >>
  `nagSize (a2 ⊕ g00) < nagSize (a1 ⊕ (a2 ⊕ g00))` by simp[] >>
  `wfnag (a2 ⊕ g00)` by fs[wfnag_add_action] >>
  metis_tac[])

val nagER_unique = store_thm(
  "nagER_unique",
  ``∀g m0 m1 m2. wfnag g ∧ nagER m0 g m1 ∧ nagER m0 g m2 ⇒ (m1 = m2)``,
  gen_tac >> completeInduct_on `nagSize g` >> qx_gen_tac `g` >> strip_tac >>
  map_every qx_gen_tac [`m0`, `m1`, `m2`] >> rw[] >> fs[PULL_FORALL] >>
  Q.UNDISCH_THEN `nagER m0 g m1` mp_tac >>
  simp[Once nagER_cases] >> rpt strip_tac
  >- (rw[] >> fs[Once nagER_cases])
  >- (rw[] >> fs[wfnag_add_action,wfnnode_def] >>
      qmatch_assum_rename_tac `adata a1 = DN d1` [] >>
      qabbrev_tac `a1' = polydata_upd (K d1) a1` >>
      qmatch_assum_rename_tac `wfnag g1` [] >>
      Q.UNDISCH_THEN `nagER m0 (a1 ⊕ g1) m2` mp_tac >>
      simp[Once nagER_cases] >> strip_tac
      >- (qmatch_assum_rename_tac `a1 ⊕ g1 = a2 ⊕ g2` [] >>
          Cases_on `a1 = a2`
          >- (rw[] >> qpat_assum `a1 ⊕ g1 = a1 ⊕ g2` mp_tac >>
              simp[] >> rw[] >> fs[] >> metis_tac [DECIDE ``x < 1n + x``]) >>
          qmatch_assum_rename_tac `adata a2 = DN d2` [] >>
          qabbrev_tac `a2' = polydata_upd (K d2) a2` >>
          `∃g00. g1 = a2 ⊕ g00 ∧ g2 = a1 ⊕ g00 ∧
                 a1 ≁ₜ a2 ∧ a1.ident ∉ idents g00 ∧
                 a2.ident ∉ idents g00`
            by metis_tac[double_graph_decomposition] >>
          rw[] >>
          `(∃m1'. nagER (apply_action a2' (apply_action a1' m0)) g00 m1') ∧
           (∃m2'. nagER (apply_action a1' (apply_action a2' m0)) g00 m2')`
            by metis_tac[nagER_total] >>
          `nagER (apply_action a1' m0) (a2 ⊕ g00) m1' ∧
           nagER (apply_action a2' m0) (a1 ⊕ g00) m2'`
             by (conj_tac >> match_mp_tac (List.nth(CONJUNCTS nagER_rules, 1)) >>
                 simp[] >> fs[idents_add_action]) >>
          `apply_action a2' (apply_action a1' m0) =
           apply_action a1' (apply_action a2' m0)`
            by (match_mp_tac apply_action_commutes >>
                simp[Abbr`a1'`, Abbr`a2'`]) >>
          pop_assum SUBST_ALL_TAC >>
          `nagSize g00 < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
          `wfnag g00` by fs[wfnag_add_action,wfnnode_def] >>
          `m2' = m1'` by metis_tac[] >>
          `nagSize (a2 ⊕ g00) < 1 + nagSize (a2 ⊕ g00) ∧
           nagSize (a1 ⊕ g00) < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
          `wfnag (a1 ⊕ g00)` by simp[wfnag_add_action,wfnnode_def] >>
          metis_tac[]) >>
      qmatch_assum_rename_tac `adata a2 = DG g0` [] >>
      `a1 ≠ a2` by (strip_tac >> fs[]) >>
      qmatch_assum_rename_tac `a1 ⊕ g1 = a2 ⊕ g2` [] >>
      `∃g00. g1 = a2 ⊕ g00 ∧ g2 = a1 ⊕ g00 ∧
             a1 ≁ₜ a2 ∧ a1.ident ∉ idents g00 ∧
             a2.ident ∉ idents g00`
        by metis_tac[double_graph_decomposition] >>
      rw[] >>
      qmatch_assum_rename_tac `nagER m0 g0 m00` [] >>
      `∃mm01 mm. nagER (apply_action a1' m0) g0 mm01 ∧
                 nagER mm01 g00 mm`
        by metis_tac [nagER_total] >>
      `nagER (apply_action a1' m0) (a2 ⊕ g00) mm`
        by (match_mp_tac (last (CONJUNCTS nagER_rules)) >>
            simp[] >> metis_tac[]) >>
      `m1 = mm` by metis_tac[DECIDE ``x < 1n + x``] >>
      pop_assum SUBST_ALL_TAC >>
      `∀b. b ∈ g0 ⇒ b ≁ₜ a1'`
        by (simp[Abbr`a1'`] >> fs[wfnag_add_action,wfnnode_def] >>
            metis_tac[gtouches_lemma, touches_SYM]) >>
      `wfnag g0` by fs[wfnag_add_action,wfnnode_def] >>
      `∃mm02. nagER m0 g0 mm02 ∧ mm01 = apply_action a1' mm02`
        by metis_tac[apply_action_nagER_commutes] >>
      pop_assum SUBST_ALL_TAC >>
      `nagSize g0 < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
      `m00 = mm02` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
      `nagER mm02 (a1 ⊕ g00) mm`
        by (match_mp_tac (List.nth(CONJUNCTS nagER_rules, 1)) >>
            simp[]) >>
      `nagSize (a1 ⊕ g00) < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
      `wfnag (a1 ⊕ g00)` by fs[wfnag_add_action,wfnnode_def] >>
      metis_tac[])
  >- (qmatch_assum_rename_tac `adata a1 = DG g0` [] >>
      qmatch_assum_rename_tac `nagER m0 g0 m00` [] >>
      qmatch_assum_rename_tac `g = a1 ⊕ g1` [] >>
      Q.UNDISCH_THEN `nagER m0 g m2` mp_tac >>
      simp[Once nagER_cases] >> strip_tac
      >- metis_tac[action_graph_case] >>
      qmatch_assum_rename_tac `nagER m02 g2 m2` [] >>
      qmatch_assum_rename_tac `nagER m0 g02 m02` [] >>
      qmatch_assum_rename_tac `nagER m01 g1 m1` [] >>
      qmatch_assum_rename_tac `nagER m0 g01 m01` [] >>
      rw[] >> fs[wfnag_add_action,wfnnode_def] >>
      qmatch_assum_rename_tac `a2.ident ∉ idents g2` [] >>
      Cases_on `a1 = a2`
      >- (Q.UNDISCH_THEN `a1 ⊕ g1 = a2 ⊕ g2` mp_tac >>
          fs[] >> rw[] >>
          `nagSize g01 < 1 + nagSize g01 + nagSize g1 ∧
           nagSize g1 < 1 + nagSize g01 + nagSize g1`
            by simp[] >>
          metis_tac[]) >>
      `∃g00.
           g1 = a2 ⊕ g00 ∧ g2 = a1 ⊕ g00 ∧
           a1 ≁ₜ a2 ∧ a1.ident ∉ idents g00 ∧
           a2.ident ∉ idents g00`
        by metis_tac[double_graph_decomposition] >>
      rw[] >>
      `∃m00. nagER m01 g02 m00` by metis_tac[nagER_total] >>
      fs[wfnag_add_action,wfnnode_def] >>
      `¬gtouches g01 g02` by metis_tac[gtouches_lemma3] >>
      `∃m02'. nagER m0 g02 m02' ∧ nagER m02' g01 m00`
        by metis_tac[nagER_commutes] >>
      `nagSize g02 < 1 + nagSize g01 + (1 + nagSize g02 + nagSize g00)`
        by simp[] >>
      `m02' = m02` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
      `∃mm. nagER m00 g00 mm` by metis_tac[nagER_total] >>
      `nagER m02 (a1 ⊕ g00) mm` by metis_tac[nagER_rules] >>
      `wfnag (a1 ⊕ g00)` by simp[wfnag_add_action,wfnnode_def] >>
      first_assum (qspecl_then [`a1 ⊕ g00`, `m02`, `mm`, `m2`] mp_tac) >>
      simp[] >> disch_then SUBST_ALL_TAC >>
      `nagER m01 (a2 ⊕ g00) m2` by metis_tac[nagER_rules] >>
      `wfnag (a2 ⊕ g00)` by simp[wfnag_add_action,wfnnode_def] >>
      first_x_assum (qspecl_then [`a2 ⊕ g00`, `m01`, `m1`, `m2`] mp_tac) >>
      simp[]))

val nagEval_def = Define`nagEval g m0 = @m. nagER m0 g m`

val nagEval_empty = store_thm(
  "nagEval_empty[simp]",
  ``nagEval emptyG m = m``,
  simp[nagEval_def, Once nagER_cases])

val nagEval_thm = store_thm(
  "nagEval_thm",
  ``(nagEval emptyG m = m) ∧
    (wfnag (a ⊕ g) ∧ a.ident ∉ idents g ⇒
     nagEval (a ⊕ g) m =
       case a.data of
           DN d => nagEval g (apply_action (polydata_upd (K d) a) m)
         | DG g0 => nagEval g (nagEval g0 m))``,
  simp[] >> strip_tac >> simp[nagEval_def] >>
  Cases_on `a.data` >> simp[]
  >- (`∃m1. nagER (apply_action (polydata_upd (K d) a) m) g m1`
         by metis_tac[nagER_total] >>
      `nagER m (a ⊕ g) m1` by simp[nagER_rules] >>
      `wfnag g` by fs[wfnag_add_action] >>
      `(∀m'. nagER m (a ⊕ g) m' ⇔ m' = m1) ∧
       (∀m'. nagER (apply_action (polydata_upd (K d) a) m) g m' ⇔ m' = m1)`
         by metis_tac[nagER_unique] >>
      simp[]) >>
  qmatch_assum_rename_tac `adata a = DG g0` [] >>
  `∃m00 mm. nagER m g0 m00 ∧ nagER m00 g mm` by metis_tac [nagER_total] >>
  `nagER m (a ⊕ g) mm` by metis_tac[nagER_rules] >>
  `wfnag g ∧ wfnag g0` by fs[wfnag_add_action,wfnnode_def] >>
  `(∀m'. nagER m g0 m' ⇔ m' = m00) ∧ (∀m'. nagER m00 g m' ⇔ m' = mm) ∧
   (∀m'. nagER m (a ⊕ g) m' ⇔ m' = mm)`
    by metis_tac[nagER_unique] >> simp[])

val _ = overload_on ("mkNN", ``polydata_upd DN``)

val stmt_weight_ssubst = store_thm(
  "stmt_weight_ssubst[simp]",
  ``stmt_weight (K 0) (K 0) (ssubst vnm v s) = stmt_weight (K 0) (K 0) s``,
  qid_spec_tac `s` >> ho_match_mp_tac PseudoCTheory.stmt_induction >>
  simp[PseudoCTheory.ssubst_def, MAP_MAP_o, combinTheory.o_DEF,
       Cong (REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG)] >> rpt strip_tac >>
  Cases_on `d` >> rw[PseudoCTheory.ssubst_def]);

val ngraphOf_def = tDefine "ngraphOf" `
  (ngraphOf i0 m0 (IfStmt gd t e) =
     case evalexpr m0 gd of
         Bool T => do
                     (i,m,g) <- ngraphOf (ap2 SUC i0) m0 t;
                     SOME(i,m, mkNN (readAction i0 m0 gd) ⊕ g)
                   od
       | Bool F => do
                     (i,m,g) <- ngraphOf (ap2 SUC i0) m0 e;
                     SOME(i,m, mkNN (readAction i0 m0 gd) ⊕ g)
                   od
       | _ => NONE) ∧

  (ngraphOf i0 m0 (ForLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       (m,g,c) <-
         FOLDL (λacc v.
                 do
                   (m,g,c) <- acc ;
                   (i,m',g0) <- ngraphOf ([],0) m (ssubst vnm v body);
                   SOME (m',
                         add_postaction
                               <| reads := SET_TO_LIST (greads g0);
                                  writes := SET_TO_LIST (gwrites g0);
                                  ident := (CONS v ## (+) c) i0;
                                  data := DG g0 |>
                               g,
                         c + 1)
                 od)
               (SOME(m0,emptyG,0))
               dvs;
       SOME(ap2 ((+) (LENGTH dvs)) i0, m, g)
     od) ∧

  (ngraphOf i0 m0 (Seq cmds) =
     case cmds of
         [] => SOME(i0, m0, emptyG)
       | c :: rest =>
         do
           (i1,m1,G1) <- ngraphOf ([],0) m0 c;
           (i2,m2,G2) <- ngraphOf (ap2 SUC i0) m1 (Seq rest);
           SOME(i2,m2,<| reads := SET_TO_LIST (greads G1);
                         writes := SET_TO_LIST (gwrites G1);
                         data := DG G1; ident := i0 |> ⊕ G2)
         od) ∧

  (ngraphOf i0 m0 (ParLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       ns <- OPT_SEQUENCE (MAPi (λn v.
               do
                 (i,m,g) <- ngraphOf ([],0) m0 (ssubst vnm v body);
                 SOME(<| reads := SET_TO_LIST (greads g);
                         writes := SET_TO_LIST (gwrites g);
                         data := DG g;
                         ident := (CONS v ## (+) n) i0 |>)
               od) dvs);
       assert(∀i j. i < j ∧ j < LENGTH ns ⇒ EL i ns ≁ₜ EL j ns);
       g <- SOME (FOLDR add_action emptyG ns);
       m <- nagEval g (SOME m0);
       SOME(ap2 ((+) (LENGTH dvs)) i0, m, g)
     od) ∧

  (ngraphOf i0 m0 (Par cmds) =
     do
       ns <- OPT_SEQUENCE
         (MAPi (λn c.
                 do
                   (i,m,g) <- ngraphOf ([],0) m0 c;
                   SOME <| reads := SET_TO_LIST (greads g);
                           writes := SET_TO_LIST (gwrites g);
                           data := DG g;
                           ident := ap2 ((+) n) i0 |>
                  od)
               cmds);
       assert(∀i j. i < j ∧ j < LENGTH ns ⇒ EL i ns ≁ₜ EL j ns);
       g <- SOME(FOLDR add_action emptyG ns);
       m <- nagEval g (SOME m0);
       SOME(ap2 ((+) (LENGTH ns)) i0, m, g)
     od) ∧

  (ngraphOf i0 m0 (Assign w ds opn) =
     do
       (aname,i_e) <- SOME w;
       i <- (some i. evalexpr m0 i_e = Int i);
       rds <- getReads m0 ds;
       a0 <- SOME(mkNN (readAction i0 m0 i_e));
       a1 <- SOME(mkNN (dvreadAction (ap2 SUC i0) m0 ds));
       a <- SOME <| writes := [Array aname i];
                    reads := rds;
                    data := DN (mergeReads ds opn);
                    ident := ap2 ((+) 2) i0 |>;
       rvs <- OPT_SEQUENCE (MAP (evalDexpr m0) ds);
       m' <- upd_array m0 aname i (opn rvs);
       SOME(ap2 ((+) 3) i0, m', a0 ⊕ (a1 ⊕ (a ⊕ emptyG)))
     od) ∧

  (ngraphOf i0 m0 (AssignVar vnm e) =
     do
       m' <- updf (Variable vnm) (evalexpr m0 e) m0;
       SOME(ap2 SUC i0, m',
            <| writes := [Variable vnm];
               reads := expr_reads m0 e;
               data := DN (K (evalexpr m0 e));
               ident := i0 |> ⊕ emptyG)
     od) ∧

  (ngraphOf i0 m0 Abort = NONE) ∧

  (ngraphOf i0 m0 Done = SOME(i0,m0,emptyG)) ∧

  (ngraphOf i0 m0 (Malloc vnm sz value) = NONE)

`  (WF_REL_TAC `measure (λ(i,m,c). stmt_weight (K 0) (K 0) c)` >> simp[MAX_PLUS] >>
    rpt strip_tac >> qpat_assum `n < LENGTH cs` kall_tac >> Induct_on `cmds` >>
    dsimp[] >> rpt strip_tac >> res_tac >> simp[]);

val ngraphOf_ind = theorem "ngraphOf_ind"

val idents_FOLDR_add_action = store_thm(
  "idents_FOLDR_add_action",
  ``i ∈ idents (FOLDR add_action emptyG l) ⇔ ∃a. MEM a l ∧ i = a.ident``,
  Induct_on `l` >> simp[] >> dsimp[]);

val SND_ap1 = store_thm(
  "SND_ap1[simp]",
  ``SND (ap1 f p) = SND p``,
  Cases_on `p` >> simp[]);

val SND_ap2 = store_thm(
  "SND_ap2[simp]",
  ``SND (ap2 f p) = f (SND p)``,
  Cases_on `p` >> simp[]);

val iftac =
    simp[ngraphOf_def] >>
    map_every qx_gen_tac [`i0`, `m0`, `gd`, `th`, `el`] >>
    strip_tac >> Cases_on `evalexpr m0 gd` >> simp[] >>
    COND_CASES_TAC >> fs[PULL_EXISTS, FORALL_PROD]

val FOLDL_FOLDR = store_thm(
  "FOLDL_FOLDR",
  ``∀l a. FOLDL f a l = FOLDR (combin$C f) a (REVERSE l)``,
  Induct_on `l` >> simp[rich_listTheory.FOLDR_APPEND]);

val forloopf_def = Define`
  forloopf vnm body vs (it:num) v acc =
    do
      (m',g',c) <- acc;
      (i,m',g0) <-
        ngraphOf ([],0) m' (ssubst vnm v body);
      SOME
        (m',
         add_postaction
           <|writes := SET_TO_LIST (gwrites g0);
             reads := SET_TO_LIST (greads g0); data := DG g0;
             ident := (v::vs,c + it)|> g',c + 1)
    od
`;

val FOLDR_forloopf_c = store_thm(
  "FOLDR_forloopf_c",
  ``∀m g c.
      FOLDR (forloopf vnm body vs0 it0) (SOME(m0,emptyG,0)) dvs =
      SOME(m,g,c) ⇒ LENGTH dvs = c``,
  Induct_on `dvs` >> simp[forloopf_def,PULL_EXISTS, FORALL_PROD] >>
  rpt strip_tac >> lfs[]);

val FOLDR_forloopf_idents = store_thm(
  "FOLDR_forloopf_idents",
  ``∀m g c.
      FOLDR (forloopf vnm body vs0 it0) (SOME(m0,emptyG,0)) dvs =
      SOME(m,g,c) ⇒
      ∀us i. (us,i) ∈ idents g ⇒ it0 ≤ i ∧ i < c + it0``,
  Induct_on `dvs` >> simp[forloopf_def, PULL_EXISTS, FORALL_PROD] >>
  rpt strip_tac >> fs[] >> simp[] >> res_tac >> simp[]);

val C1 = store_thm(
  "C1",
  ``combin$C (\x y. f x y) = \y x. f x y``,
  simp[FUN_EQ_THM]);

val ngraphOf_idents = store_thm(
  "ngraphOf_idents",
  ``∀i0 m0 c0 i m g.
      ngraphOf i0 m0 c0 = SOME(i,m,g) ⇒
      SND i0 ≤ SND i ∧
      ∀it. it ∈ idents g ⇒ SND i0 ≤ SND it ∧ SND it < SND i``,
  ho_match_mp_tac ngraphOf_ind >> rpt conj_tac
  >- ((* if *) iftac >> rpt strip_tac >> res_tac >> rw[] >> simp[])
  >- ((* forloop *)
      simp[ngraphOf_def, PULL_EXISTS, FORALL_PROD] >>
      map_every qx_gen_tac [`vs`, `n`, `m0`, `vnm`, `d`, `body`] >>
      disch_then kall_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
      qpat_assum `dvalues xx yy = zz` kall_tac >>
      pop_assum mp_tac >> simp[FOLDL_FOLDR, GSYM forloopf_def, C1] >>
      simp_tac (srw_ss() ++ ETA_ss) [] >>
      qabbrev_tac `dvs' = REVERSE dvs` >>
      `LENGTH dvs = LENGTH dvs'` by simp[Abbr`dvs'`] >>
      pop_assum (fn th=> simp[th]) >>
      qmatch_abbrev_tac `FOLDR ff (SOME(m0,emptyG,0n)) dvs' = SOME(m,g,c) ⇒
                         (us,p) ∈ idents g ⇒ n ≤ p ∧ p < n + LENGTH dvs'` >>
      qunabbrev_tac `ff` >> markerLib.RM_ALL_ABBREVS_TAC >>
      `∀m g c.
         FOLDR (forloopf vnm body vs n) (SOME (m0,emptyG,0)) dvs' =
         SOME(m,g,c) ⇒
         ((us,p) ∈ idents g ⇒ n ≤ p ∧ p < n + LENGTH dvs') ∧
         LENGTH dvs' = c`
        suffices_by metis_tac[] >>
      Induct_on `dvs'` >>
      simp[forloopf_def, PULL_EXISTS, FORALL_PROD] >> csimp[] >>
      rpt strip_tac >> rw[] >> simp[] >> lfs[])
  >- ((* seq *)
      map_every qx_gen_tac [`i0`, `m0`, `cs`] >> strip_tac >>
      simp[Once ngraphOf_def] >>
      Cases_on `cs` >> simp[PULL_EXISTS, FORALL_PROD] >> fs[] >>
      Cases_on `i0` >> fs[FORALL_PROD] >> rpt strip_tac >> res_tac >>
      metis_tac[DECIDE ``x ≤ x ∧ (SUC x ≤ y ⇒ x ≤ y) ∧
                         (SUC x ≤ y ⇒ x < y)``])
  >- ((* parloop *)
      map_every qx_gen_tac [`i0`, `m0`, `vnm`, `d`, `body`] >>
      strip_tac >>
      simp[ngraphOf_def, PULL_EXISTS, OPT_SEQUENCE_EQ_SOME,
           MAP_MAP_o, combinTheory.o_ABS_R, MEM_MAPi,
           EL_MAP, EXISTS_PROD] >> rpt gen_tac >> strip_tac >>
      rpt (first_x_assum (kall_tac o
                          assert (equal 2 o length o #1 o strip_forall o
                                  concl))) >>
      simp[idents_FOLDR_add_action, MEM_MAPi, PULL_EXISTS] >>
      rpt strip_tac >> res_tac >> simp[])
  >- ((* par *)
      map_every qx_gen_tac [`i0`, `m0`, `cmds`] >> strip_tac >>
      simp[ngraphOf_def, PULL_EXISTS, OPT_SEQUENCE_EQ_SOME,
           combinTheory.o_ABS_R, idents_FOLDR_add_action,
           MEM_MAPi, EXISTS_PROD] >> rpt strip_tac >> res_tac >>
      simp[])
  >- ((* assign *)
      simp[ngraphOf_def, FORALL_PROD, PULL_EXISTS] >> rw[] >> simp[])
  >- ((* assignvar *)
      simp[ngraphOf_def, FORALL_PROD, PULL_EXISTS])
  >- ((* abort *) simp[ngraphOf_def])
  >- ((* Done *) simp[ngraphOf_def])
  >- ((* malloc *) simp[ngraphOf_def]))

val FINITE_greadswrites = store_thm(
  "FINITE_greadswrites[simp]",
  ``∀g. FINITE (greads g) ∧ FINITE (gwrites g)``,
  ho_match_mp_tac graph_ind >> simp[]);

val wfnag_add_postaction = store_thm(
  "wfnag_add_postaction",
  ``a.ident ∉ idents g ⇒
    (wfnag (add_postaction a g) ⇔ wfnag g ∧ wfnnode a)``,
  simp[wfnnode_def] >> simp[Once wfnag_cases, SimpLHS] >> dsimp[] >>
  simp[Once wfnag_cases, SimpRHS, SimpL ``$/\``] >>
  Cases_on `a.data` >> dsimp[] >> metis_tac[]);

val wfnag_FOLDR_add_action_I = store_thm(
  "wfnag_FOLDR_add_action_I",
  ``(∀a. MEM a l ⇒ wfnnode a) ⇒ wfnag (FOLDR add_action emptyG l)``,
  Induct_on `l` >> dsimp[] >> qx_gen_tac `h` >>
  Cases_on `h.ident ∈ idents (FOLDR add_action emptyG l)`
  >- simp[add_action_id |> EQ_IMP_RULE |> #2] >>
  simp[wfnag_add_action]);

val nagEval_COND = store_thm(
  "nagEval_COND",
  ``wfnag (a ⊕ g) ⇒
    nagEval (a ⊕ g) m = if a.ident ∈ idents g then nagEval g m
                        else
                          case a.data of
                              DN d => nagEval g (apply_action (polydata_upd (K d) a) m)
                            | DG g0 => nagEval g (nagEval g0 m)``,
  strip_tac >> rw[] >- simp[add_action_id |> EQ_IMP_RULE |> #2] >>
  simp[nagEval_thm]);

val wfnag_COND = store_thm(
  "wfnag_COND",
  ``wfnag (a ⊕ g) ⇔ wfnag g ∧ (a.ident ∈ idents g ∨ wfnnode a)``,
  Cases_on `a.ident ∈ idents g` >- simp[add_action_id |> EQ_IMP_RULE |> #2] >>
  simp[wfnag_add_action]);

val wfnag_post_COND = store_thm(
  "wfnag_post_COND",
  ``wfnag (add_postaction a g) ⇔ wfnag g ∧ (a.ident ∈ idents g ∨ wfnnode a)``,
  Cases_on `a.ident ∈ idents g` >-simp[add_postactionID] >>
  simp[wfnag_add_postaction]);

val wfnag_merge_graph = store_thm(
  "wfnag_merge_graph",
  ``∀g2 g1. wfnag g1 ∧ wfnag g2 ⇒ wfnag (merge_graph g1 g2)``,
  ho_match_mp_tac graph_ind >> simp[merge_graph_thm] >>
  simp[wfnag_add_action] >> rpt strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  Cases_on `a.ident ∈ idents g1` >>
  simp[add_postactionID, wfnag_add_postaction]);

val wfnnode_mkNN = store_thm(
  "wfnnode_mkNN[simp]",
  ``wfnnode (mkNN a)``,
  simp[wfnnode_def, polydata_upd_def]);

val ngraphOf_wfnag = store_thm(
  "ngraphOf_wfnag",
  ``∀i0 m0 c0 i m g. ngraphOf i0 m0 c0 = SOME(i,m,g) ⇒ wfnag g``,
  ho_match_mp_tac ngraphOf_ind >> rpt conj_tac
  >- ((* if *) iftac >> rpt strip_tac >> res_tac >>
      qmatch_assum_rename_tac `wfnag g` [] >>
      `∀i. i ∈ idents g ⇒ SUC (SND i0) ≤ SND i`
        by metis_tac[SND_ap2, ngraphOf_idents] >>
      `i0 ∉ idents g` by (strip_tac >> res_tac >> lfs[]) >>
      simp[wfnag_add_action])
  >- ((* forloop *)
      simp[ngraphOf_def, PULL_EXISTS, FORALL_PROD, FOLDL_FOLDR,
           GSYM forloopf_def, C1] >>
      simp_tac (bool_ss ++ ETA_ss) [] >>
      map_every qx_gen_tac [`vs`, `i`, `m0`, `vnm`, `d`, `body`] >>
      rpt gen_tac >> strip_tac >>
      map_every qx_gen_tac [`m`, `g`, `dvs`, `c`] >>
      strip_tac >> fs[] >>
      qpat_assum `dvalues xx yy = zz` kall_tac >>
      qabbrev_tac `dvs' = REVERSE dvs` >>
      `∀e. MEM e dvs ⇔ MEM e dvs'` by simp[Abbr`dvs'`] >> fs[] >>
      pop_assum kall_tac >> markerLib.RM_ABBREV_TAC "dvs'" >>
      pop_assum mp_tac >> map_every qid_spec_tac [`m`, `g`, `c`] >>
      Induct_on `dvs'` >> simp[] >>
      qx_gen_tac `h` >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      strip_tac >> pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      simp[forloopf_def, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >> fs[] >>
      res_tac >> simp[wfnag_post_COND, wfnnode_def, SET_TO_LIST_INV])
  >- ((* seq *)
      map_every qx_gen_tac [`i0`, `m0`, `cs`] >> strip_tac >>
      simp[Once ngraphOf_def] >> Cases_on `cs` >> fs[] >>
      simp[PULL_EXISTS, FORALL_PROD, wfnag_COND, wfnnode_def,
           SET_TO_LIST_INV])
  >- ((* parloop *)
      map_every qx_gen_tac [`i0`, `m0`, `vnm`, `d`, `body`] >> strip_tac >>
      simp[ngraphOf_def, PULL_EXISTS, OPT_SEQUENCE_EQ_SOME, combinTheory.o_ABS_R,
           MEM_MAPi, EXISTS_PROD] >>
      rpt strip_tac >> match_mp_tac wfnag_FOLDR_add_action_I >>
      simp[MEM_MAPi, PULL_EXISTS] >> rpt strip_tac >> res_tac >> simp[] >>
      simp[wfnag_add_action, SET_TO_LIST_INV, wfnnode_def] >>
      metis_tac[rich_listTheory.EL_MEM])
  >- ((* par *)
      simp[ngraphOf_def, PULL_EXISTS, FORALL_PROD, OPT_SEQUENCE_EQ_SOME,
           combinTheory.o_ABS_R, MEM_MAPi, EXISTS_PROD] >>
      rpt strip_tac >> match_mp_tac wfnag_FOLDR_add_action_I >>
      simp[MEM_MAPi, PULL_EXISTS] >> rpt strip_tac >> res_tac >>
      simp[SET_TO_LIST_INV, wfnag_add_action, wfnnode_def] >>
      metis_tac[rich_listTheory.EL_MEM])
  >- ((* assign *)
      simp[ngraphOf_def, FORALL_PROD, PULL_EXISTS, wfnag_add_action, wfnnode_def])
  >- ((* assignvar *)
      simp[ngraphOf_def, FORALL_PROD, PULL_EXISTS, wfnag_add_action,
           polydata_upd_def, wfnnode_def])
  >- ((* abort *) simp[ngraphOf_def])
  >- ((* done *) simp[ngraphOf_def])
  >- ((* malloc *) simp[ngraphOf_def]))

val mkNN_data = store_thm(
  "mkNN_data[simp]",
  ``adata (mkNN a) = DN a.data``,
  simp[polydata_upd_def]);

val polydata_updK = store_thm(
  "polydata_updK[simp]",
  ``polydata_upd (K (adata a)) (mkNN a) = a``,
  simp[polydata_upd_def, action_component_equality]);

val apply_action_readAction = store_thm(
  "apply_action_readAction[simp]",
  ``apply_action (readAction i m e) mem = mem``,
  simp[apply_action_def, readAction_def]);

val nagEval_postaction = store_thm(
  "nagEval_postaction",
  ``wfnnode a ∧ wfnag g ⇒
    nagEval (add_postaction a g) m =
      if a.ident ∈ idents g then nagEval g m
      else (case a.data of
                DN d => apply_action (polydata_upd (K d) a)
              | DG g0 => nagEval g0) (nagEval g m)``,
  Cases_on `a.ident ∈ idents g` >- simp[add_postactionID] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`m`, `a`, `g`] >> ho_match_mp_tac graph_ind >>
  simp[] >> conj_tac >- (simp[nagEval_COND, wfnag_add_action] >> rpt gen_tac >>
                         Cases_on `a.data` >> simp[]) >>
  simp[wfnag_add_action] >>
  rpt strip_tac >> simp[actionGraphTheory.add_action_add_postaction_ASSOC,
                        nagEval_COND, idents_add_postaction, wfnag_add_action,
                        wfnag_add_postaction] >>
  Cases_on `adata a` >> simp[]);

val nagEval_merge_graph = store_thm(
  "nagEval_merge_graph",
  ``∀g2 g1. wfnag g1 ∧ wfnag g2 ∧ DISJOINT (idents g1) (idents g2) ⇒
            nagEval (merge_graph g1 g2) m = nagEval g2 (nagEval g1 m)``,
  ho_match_mp_tac graph_ind >>
  simp[merge_graph_thm, wfnag_add_action, nagEval_COND] >> rpt strip_tac >>
  simp[wfnag_add_postaction, nagEval_postaction] >> Cases_on `adata a` >> simp[]);

val nagEval_ngraphOf = store_thm(
  "nagEval_ngraphOf",
  ``∀i0 m0 c0 i m g.
      ngraphOf i0 m0 c0 = SOME(i,m,g) ⇒
      nagEval g (SOME m0) = SOME m``,
  ho_match_mp_tac ngraphOf_ind >> rpt conj_tac
  >- ((* if *)
      iftac >> map_every qx_gen_tac [`us`, `i`, `m`, `g`] >>
      strip_tac >> res_tac >> `wfnag g` by metis_tac[ngraphOf_wfnag] >>
      simp[nagEval_COND,wfnag_COND])
  >- ((* forloop *)
      simp[ngraphOf_def, PULL_EXISTS, FORALL_PROD, GSYM forloopf_def,
           FOLDL_FOLDR, C1] >>
      simp_tac (bool_ss ++ ETA_ss) [] >>
      map_every qx_gen_tac [`us`, `i0`, `m0`, `vnm`, `d`, `body`] >> strip_tac >>
      map_every qx_gen_tac [`m`, `g`, `dvs`, `c`] >> strip_tac >> fs[] >>
      qpat_assum `dvalues xx yy = zz` kall_tac >>
      qabbrev_tac `dvs' = REVERSE dvs` >>
      `∀e. MEM e dvs ⇔ MEM e dvs'` by simp[Abbr`dvs'`] >> fs[] >>
      pop_assum kall_tac >> markerLib.RM_ABBREV_TAC "dvs'" >>
      pop_assum mp_tac >>
      `∀m g c.
         FOLDR (forloopf vnm body us i0) (SOME(m0,emptyG,0)) dvs' =
         SOME(m,g,c) ⇒
         wfnag g ∧
         (∀vs j. (vs,j) ∈ idents g ⇒ j < c + i0) ∧
         nagEval g (SOME m0) = SOME m` suffices_by metis_tac[] >>
      Induct_on `dvs'` >> simp[] >> qx_gen_tac `h` >>
      simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
      pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      simp[forloopf_def, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
      fs[]
      >- (imp_res_tac ngraphOf_wfnag >>
          simp[wfnag_post_COND, wfnnode_def, SET_TO_LIST_INV])
      >- (res_tac >> simp[]) >>
      qmatch_assum_rename_tac
        `FOLDR FF XX YY = SOME(mm,gg,c)` ["FF", "XX", "YY"] >>
      `∀vs. (vs,i0+c) ∉ idents gg` by (rpt strip_tac >> res_tac >> fs[]) >>
      imp_res_tac ngraphOf_wfnag >> lfs[] >>
      simp[nagEval_postaction, wfnnode_def, SET_TO_LIST_INV])
  >- ((* seq *)
      map_every qx_gen_tac [`i0`, `m0`, `cmds`] >> strip_tac >>
      simp[Once ngraphOf_def] >> Cases_on `cmds` >>
      simp[PULL_EXISTS,FORALL_PROD] >> fs[] >> rpt strip_tac >>
      qmatch_assum_rename_tac `ngraphOf ([],0) m0 c = SOME((us,i), cm, cg)` []>>
      qmatch_assum_rename_tac
        `ngraphOf (ap2 SUC i0) cm (Seq cs) = SOME((vs,j), csm, csg)` [] >>
      fs[] >>
      `∀vs k. (vs,k) ∈ idents csg ⇒ SUC (SND i0) ≤ k`
        by (imp_res_tac ngraphOf_idents >> rpt strip_tac >> res_tac >>
            lfs[]) >>
      `i0 ∉ idents csg` by (Cases_on `i0` >> strip_tac >> res_tac >> lfs[]) >>
      imp_res_tac ngraphOf_wfnag >>
      simp[nagEval_COND,wfnag_COND,wfnnode_def,SET_TO_LIST_INV])
  >- ((* parloop *)
      rpt gen_tac >> strip_tac >> simp[ngraphOf_def, PULL_EXISTS])
  >- ((* par *) simp[ngraphOf_def, PULL_EXISTS])
  >- ((* assign *)
      simp[ngraphOf_def, FORALL_PROD, PULL_EXISTS, nagEval_thm,
           wfnag_add_action, wfnnode_def] >>
      simp[polydata_upd_def, apply_action_def, updf_def,
           mergeReads_def] >>
      metis_tac[assign_lemma, listTheory.REVERSE_DEF, APPEND])
  >- ((* assign var *)
      simp[ngraphOf_def, nagEval_thm, wfnag_add_action, wfnnode_def,
           polydata_upd_def, apply_action_def])
  >- ((* abort *) simp[ngraphOf_def])
  >- ((* done *) simp[ngraphOf_def])
  >- ((* malloc *) simp[ngraphOf_def]));

val ngraphOf_Done = save_thm(
  "ngraphOf_Done[simp]",
  last (#1 (front_last (CONJUNCTS ngraphOf_def))))

val mkNN_identupd = store_thm(
  "mkNN_identupd[simp]",
  ``mkNN a with ident updated_by f = mkNN (a with ident updated_by f)``,
  simp[polydata_upd_def]);

val readAction_identupd = store_thm(
  "readAction_identupd[simp]",
  ``readAction i m e with ident updated_by f = readAction (f i) m e``,
  simp[readAction_def]);
(*
val ngraph_starting_id_irrelevant = store_thm(
  "ngraph_starting_id_irrelevant",
  ``∀i0 m0 c i m g.
       ngraphOf i0 m0 c = SOME(i,m,g) ⇒
       ∀i0'. ∃f.
         INJ f (idents g) UNIV ∧ f i0 = i0' ∧
         ngraphOf i0' m0 c = SOME(f i,m,imap f g)``,
  ho_match_mp_tac ngraphOf_ind >> rpt conj_tac
  >- ((* if *) iftac >> simp[EXISTS_PROD] >>
      `∃vs0 it0. i0 = (vs0,it0)` by metis_tac[pair_CASES] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      map_every qx_gen_tac [`vs'`, `it'`, `m`, `g'`] >> strip_tac >>
      fs[] >> map_every qx_gen_tac [`vs0'`, `it0'`] >>
      first_x_assum (qspecl_then [`vs0'`, `SUC it0'`] strip_assume_tac) >>
      csimp[imap_add_action] >>
      qexists_tac `λj. if j = (vs0,it0) then (vs0',it0') else f j` >>
      simp[INJ_INSERT] >>
      `(∀j. j ∈ idents g' ⇒ j ≠ (vs0,it0)) ∧ it' ≠ it0`
        by (imp_res_tac ngraphOf_idents >> rpt strip_tac >> res_tac >>
            rw[] >> lfs[]) >>
      csimp[Cong INJ_CONG, Cong imap_CONG] >>
      asm_simp_tac (srw_ss() ++ ETA_ss) [] >>
      `∀j. j ∈ idents g' ⇒ f j ≠ (vs0',it0')`
        suffices_by metis_tac[pair_CASES] >> rpt strip_tac >>
      `f j ∈ idents (imap f g')` by (simp[idents_imap] >> metis_tac[]) >>
      first_x_assum (mp_tac o MATCH_MP ngraphOf_idents) >> simp[] >>
      metis_tac[SND, DECIDE ``x:num ≤ x``])
  >- ((* forloop *)
      simp[ngraphOf_def, PULL_EXISTS, EXISTS_PROD, FORALL_PROD] >>
      map_every qx_gen_tac [`vs0`, `it0`, `m0`, `vnm`, `d`, `body`] >>
      strip_tac >>
      map_every qx_gen_tac [`m`, `g`, `dvs`, `c`] >>
      simp[FOLDL_FOLDR] >> strip_tac >>
      fs[GSYM forloopf_def, C1] >>
      full_simp_tac (srw_ss() ++ ETA_ss) [] >>
      map_every qx_gen_tac [`vs'`, `it'`] >>
      qpat_assum `dvalues xx yy = zz` kall_tac >>
      qabbrev_tac `dvs' = REVERSE dvs` >>
      `LENGTH dvs = LENGTH dvs'` by simp[Abbr`dvs'`] >>
      pop_assum (fn th => simp[th]) >>
      `∀v. MEM v dvs ⇔ MEM v dvs'` by simp[Abbr`dvs'`] >>
      pop_assum (fn th => fs[th]) >>
      markerLib.RM_ABBREV_TAC "dvs'" >>
      pop_assum mp_tac >> map_every qid_spec_tac [`m`, `g`, `c`] >>
      Induct_on `dvs'` >> simp[]
      >- (rw[] >> simp[] >> qexists_tac `K (vs',it')` >> simp[]) >>
      qx_gen_tac `h` >>
      simp[PULL_EXISTS, EXISTS_PROD, forloopf_def, DISJ_IMP_THM,
           FORALL_AND_THM] >> strip_tac >>
      map_every qx_gen_tac [`hm`, `m`, `g`, `c`, `hvs`, `hit`, `hg`] >>
      pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      strip_tac >> first_x_assum (qspecl_then [`c`, `g`, `m`] mp_tac) >>
      simp[] >> disch_then (qx_choosel_then [`f`, `cc`] strip_assume_tac) >>
      first_x_assum (qspec_then `m` mp_tac) >> simp[] >> strip_tac >>
      csimp[imap_add_postaction] >> simp[INJ_INSERT]
*)

val CI = prove(``(\a b. f b a) = combin$C f``, simp[FUN_EQ_THM])

val gtouches_ALT = store_thm(
  "gtouches_ALT",
  ``gtouches g1 g2 ⇔
      ¬DISJOINT (gwrites g1) (gwrites g2) ∨
      ¬DISJOINT (gwrites g1) (greads g2) ∨
      ¬DISJOINT (gwrites g2) (greads g1)``,
  simp[gtouches_def, EQ_IMP_THM, PULL_EXISTS, touches_def] >> conj_tac
  >- (map_every qx_gen_tac [`a`, `b`] >> strip_tac
      >- (disj1_tac >> simp[DISJOINT_DEF, Once EXTENSION, gwrites_def,
                            PULL_EXISTS] >> metis_tac[])
      >- (disj2_tac >> disj1_tac >>
          simp[DISJOINT_DEF, Once EXTENSION, gwrites_def,
               greads_def, PULL_EXISTS] >> metis_tac[]) >>
      rpt disj2_tac >>
      simp[DISJOINT_DEF, Once EXTENSION, gwrites_def,
           greads_def, PULL_EXISTS] >> metis_tac[]) >>
  strip_tac >> fs[DISJOINT_DEF, Once EXTENSION, PULL_EXISTS,
                  gwrites_def, greads_def] >> metis_tac[]);

val gtle_def = Define`
  gtle g1 g2 ⇔ greads g1 ⊆ greads g2 ∧ gwrites g1 ⊆ gwrites g2
`;

val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450),
                            term_name = "gtle",
                            tok = "≤ₜ"}

val gtle_REFL = store_thm(
  "gtle_REFL[simp]",
  ``g ≤ₜ g``,
  simp[gtle_def]);

val gtle_TRANS = store_thm(
  "gtle_TRANS",
  ``g1 ≤ₜ g2 ∧ g2 ≤ₜ g3 ⇒ g1 ≤ₜ g3``,
  simp[gtle_def] >> metis_tac[SUBSET_TRANS]);

val gtle_touches = store_thm(
  "gtle_touches",
  ``g1 ≤ₜ g2 ⇒ ∀g. gtouches g g1 ⇒ gtouches g g2``,
  simp[gtouches_def] >> spose_not_then strip_assume_tac >>
  Q.UNDISCH_THEN `a1 ∼ₜ a2` mp_tac >> simp[touches_def] >>
  rpt strip_tac >> spose_not_then strip_assume_tac
  >- (`∃b. b ∈ g2 ∧ MEM w b.writes` suffices_by metis_tac[touches_def] >>
      `w ∈ gwrites g1` by (dsimp[gwrites_def] >> metis_tac[]) >>
      `w ∈ gwrites g2` by metis_tac[gtle_def, SUBSET_DEF] >>
      pop_assum mp_tac >> dsimp[gwrites_def] >> metis_tac[])
  >- (`∃b. b ∈ g2 ∧ MEM w b.reads` suffices_by metis_tac [touches_def] >>
      `w ∈ greads g1` by (dsimp[greads_def] >> metis_tac[]) >>
      `w ∈ greads g2` by metis_tac[gtle_def, SUBSET_DEF] >>
      pop_assum mp_tac >> dsimp[greads_def] >> metis_tac[])
  >- (`∃b. b ∈ g2 ∧ MEM w b.writes` suffices_by metis_tac[touches_def] >>
     `w ∈ gwrites g1` by (dsimp[gwrites_def] >> metis_tac[]) >>
     `w ∈ gwrites g2` by metis_tac[gtle_def, SUBSET_DEF] >>
     pop_assum mp_tac >> dsimp[gwrites_def] >> metis_tac[]))

(*
val eval_ngraph = prove(
  ``∀m0 c0 m c.
      (m0,c0) ---> (m,c) ⇒
      ∀i0 i1 m1 g1.
        ngraphOf i0 m0 c0 = SOME(i1,m1,g1) ⇒
        ∃i2 g2.
          ngraphOf i0 m c = SOME(i2,m1,g2) ∧
          g2 ≤ₜ g1 ∧ SND i2 = SND i1``,
  ho_match_mp_tac eval_ind' >> rpt conj_tac
  >- ((* seq takes a step *)
      map_every qx_gen_tac [`c`, `c0`] >> reverse Induct >> simp[]
      >- (ONCE_REWRITE_TAC [ngraphOf_def] >>
          simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
          fs[FORALL_PROD, EXISTS_PROD] >>
          simp[touches_def] >> metis_tac[]) >>
      ONCE_REWRITE_TAC [ngraphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
      rpt strip_tac >> res_tac >> simp[] >>
      qx_gen_tac `g'` >>
      reverse strip_tac >- simp[] >>
      `gtouches g2 (b ⊕ emptyG)`
        by (fs[touches_def, gwrites_def, greads_def]
      simp[touches_def] >> fs[gtouches_def, touches_def] >>
      metis_tac[]

metis_tac[])
  >- ((* seq is all done *)
      qx_gen_tac `m0` >> Induct >>
      ONCE_REWRITE_TAC[ngraphOf_def] >>
      simp[PULL_EXISTS, FORALL_PROD] >> fs[] >> metis_tac[])
  >- ((* if guard evaluates to bool *)
      simp[ngraphOf_def] >>
      map_every qx_gen_tac [`m0`, `gd`, `th`, `el`, `b`] >>
      Cases_on `b` >> simp[PULL_EXISTS, FORALL_PROD] ...)
  >- ((* if guard doesn't evaluate to bool *)
      rw[ngraphOf_def] >> Cases_on `evalexpr m0 g` >> simp[] >>
      fs[])
  >- ((* assign var succeeds *) simp[ngraphOf_def, updf_def])
  >- ((* assign var fails *) simp[ngraphOf_def, updf_def])
  >- ((* assign succeeds *)
      simp[ngraphOf_def, PULL_EXISTS, evalexpr_def,
          OPT_SEQUENCE_EQ_SOME, MEM_MAP, isDValue_destDValue])
  >- ((* assign fails *)
      simp[ngraphOf_def, evalexpr_def, OPT_SEQUENCE_EQ_SOME,
           isDValue_destDValue])
  >- ((* index of array assignment is evaluated *)
      simp[ngraphOf_def, PULL_EXISTS, evalexpr_def, readAction_def,
           expr_reads_def] >> rpt strip_tac (* >- fs[touches_def] >>
      metis_tac[] *))
  >- ((* array-read inside array assignment has index evaluated *)
      simp[ngraphOf_def, PULL_EXISTS, evalDexpr_def, evalexpr_def,
           OPT_SEQUENCE_EQ_SOME, MEM_MAP, getReads_APPEND,
           getReads_def] >> rpt gen_tac >>
      simp[MAP_MAP_o, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      csimp[] >> rpt strip_tac (*
      >- metis_tac[]
      >- (fs[dvreadAction_def, touches_def, dvread_def,
             expr_reads_def] >> metis_tac[])
      >- (fs[touches_def] >> metis_tac[])) *))
  >- ((* array-read inside array assignment actually reads memory *)
      dsimp[ngraphOf_def, OPT_SEQUENCE_EQ_SOME, MEM_MAP, evalDexpr_def,
            evalexpr_def] >>
      dsimp[getReads_APPEND, getReads_def] >>
      simp[touches_def, dvreadAction_def, dvread_def] >>
      metis_tac[])
  >- ((* variable read inside array assignment *)
      dsimp[ngraphOf_def, OPT_SEQUENCE_EQ_SOME, evalDexpr_def, MEM_MAP] >>
      dsimp[getReads_def, getReads_APPEND] >>
      simp[touches_def, dvreadAction_def, dvread_def] >> metis_tac[])
  >- ((* forloop turns into seq *)
      map_every qx_gen_tac [`b`, `d`, `m0`, `vnm`, `iters`] >> strip_tac >>
      simp [Once ngraphOf_def, SimpL ``$==>``] >>
      simp[GSYM forloopf_def, FORALL_PROD, EXISTS_PROD,
           PULL_EXISTS, Once CI] >>
      simp_tac (bool_ss ++ ETA_ss) [] >>
      pop_assum kall_tac >>
      map_every qx_gen_tac [`us`, `it0`, `m1`, `g1`, `c1`] >>
      qho_match_abbrev_tac `XX ⇒ P iters us it0 m0 m1 g1 c1` >>
      qunabbrev_tac `XX` >>
      `∃c0:num g0. c0 = 0 ∧
                   g0 = emptyG : (value list -> value, value list # num, actionRW) nag0`
        by simp[] >>
      rpt (pop_assum (SUBST1_TAC o SYM)) >>
      map_every qid_spec_tac [`m0`, `g0`, `c0`, `m1`, `g1`, `c1`, `us`, `it0`]>>
      `∀l us it0. FOLDL (combin$C (forloopf vnm b us it0)) NONE l = NONE`
        by (Induct >> simp[forloopf_def]) >>
      Induct_on `iters` >> simp[] >- (simp[Abbr`P`] >> simp[Once ngraphOf_def]) >>
      map_every qx_gen_tac
       [`h`, `it0`, `us`, `c1`, `g1`, `m1`, `c0`, `g0`, `m0`] >>
      strip_tac >>
      `∃m' g' c'. forloopf vnm b us it0 h (SOME(m0,g0,c0)) = SOME(m',g',c')`
        by metis_tac[NOT_NONE_SOME, option_CASES, pair_CASES] >> fs[] >>
      pop_assum mp_tac >> simp[forloopf_def, PULL_EXISTS, FORALL_PROD] >>
      res_tac >> map_every qx_gen_tac [`svs`, `si`, `sg`] >>
      pop_assum mp_tac >> ntac 3 (pop_assum kall_tac) >> simp[Abbr`P`] >>
      simp[Once ngraphOf_def, SimpR ``$==>``] >>
      simp[EXISTS_PROD] >> Cases_on `iters`
      >- (simp[] >> simp[Once ngraphOf_def]) >>
      simp[PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
      simp[Once ngraphOf_def, EXISTS_PROD]

rpt (pop_assum kall_tac)



assign_lemma
*)
val _ = export_theory();
