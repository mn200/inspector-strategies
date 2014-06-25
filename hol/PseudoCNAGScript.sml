open HolKernel Parse boolLib bossLib;

open lcsymtacs boolSimps
open pred_setTheory listTheory pairTheory
open monadsyntax

open nagTheory
open PseudoCPropsTheory
open actionGraphTheory

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
  ``a.ident ∉ idents g ⇒
    (wfnag (a ⊕ g) ⇔
       wfnag g ∧
       case a.data of
           DN d => T
         | DG g0 => wfnag g0 ∧ gwrites g0 = set a.writes ∧
                    greads g0 = set a.reads)``,
  simp[Once wfnag_cases, SimpLHS] >> dsimp[] >>
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
      csimp[wfnag_add_action] >> ntac 2 strip_tac >> fs[] >>
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
  simp[wfnag_add_action] >> ntac 2 strip_tac >>
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
  simp[wfnag_add_action] >> ntac 2 strip_tac >> fs[GSYM IMP_DISJ_THM] >>
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
  `wfnag (a1 ⊕ g00)` by fs[wfnag_add_action] >>
  `m2 = mm` by metis_tac[] >>
  pop_assum SUBST_ALL_TAC >>
  `∀b. b ∈ g0 ⇒ b ≁ₜ a2'`
    by (simp[Abbr`a2'`] >> fs[wfnag_add_action] >>
        metis_tac[gtouches_lemma, touches_SYM]) >>
  `wfnag g0` by fs[wfnag_add_action] >>
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
  >- (rw[] >> fs[wfnag_add_action] >>
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
          `wfnag g00` by fs[wfnag_add_action] >> `m2' = m1'` by metis_tac[] >>
          `nagSize (a2 ⊕ g00) < 1 + nagSize (a2 ⊕ g00) ∧
           nagSize (a1 ⊕ g00) < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
          `wfnag (a1 ⊕ g00)` by simp[wfnag_add_action] >>
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
        by (simp[Abbr`a1'`] >> fs[wfnag_add_action] >>
            metis_tac[gtouches_lemma, touches_SYM]) >>
      `wfnag g0` by fs[wfnag_add_action] >>
      `∃mm02. nagER m0 g0 mm02 ∧ mm01 = apply_action a1' mm02`
        by metis_tac[apply_action_nagER_commutes] >>
      pop_assum SUBST_ALL_TAC >>
      `nagSize g0 < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
      `m00 = mm02` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
      `nagER mm02 (a1 ⊕ g00) mm`
        by (match_mp_tac (List.nth(CONJUNCTS nagER_rules, 1)) >>
            simp[]) >>
      `nagSize (a1 ⊕ g00) < 1 + nagSize (a2 ⊕ g00)` by simp[] >>
      `wfnag (a1 ⊕ g00)` by fs[wfnag_add_action] >>
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
      rw[] >> fs[wfnag_add_action] >>
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
      fs[wfnag_add_action] >>
      `¬gtouches g01 g02` by metis_tac[gtouches_lemma3] >>
      `∃m02'. nagER m0 g02 m02' ∧ nagER m02' g01 m00`
        by metis_tac[nagER_commutes] >>
      `nagSize g02 < 1 + nagSize g01 + (1 + nagSize g02 + nagSize g00)`
        by simp[] >>
      `m02' = m02` by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
      `∃mm. nagER m00 g00 mm` by metis_tac[nagER_total] >>
      `nagER m02 (a1 ⊕ g00) mm` by metis_tac[nagER_rules] >>
      `wfnag (a1 ⊕ g00)` by simp[wfnag_add_action] >>
      first_assum (qspecl_then [`a1 ⊕ g00`, `m02`, `mm`, `m2`] mp_tac) >>
      simp[] >> disch_then SUBST_ALL_TAC >>
      `nagER m01 (a2 ⊕ g00) m2` by metis_tac[nagER_rules] >>
      `wfnag (a2 ⊕ g00)` by simp[wfnag_add_action] >>
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
  `wfnag g ∧ wfnag g0` by fs[wfnag_add_action] >>
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
       (m,g) <-
         FOLDL (λacc v.
                 case acc of
                     NONE => NONE
                   | SOME(m,g) =>
                     case ngraphOf i0 m (ssubst vnm v body) of
                         NONE => NONE
                       | SOME(_, m', g0) =>
                         SOME(m', <| reads := SET_TO_LIST (greads g0);
                                     writes := SET_TO_LIST (gwrites g0);
                                     ident := ap1 (CONS v) i0;
                                     data := DG g0 |> ⊕ g))
               (SOME (m0,emptyG))
               dvs;
       SOME(ap2 SUC i0, m, g)
     od) ∧

  (ngraphOf i0 m0 (Seq cmds) =
     case cmds of
         [] => SOME(i0, m0, emptyG)
       | c :: rest =>
         do
           (i1,m1,G1) <- ngraphOf i0 m0 c;
           (i2,m2,G2) <- ngraphOf i1 m1 (Seq rest);
           SOME(i2,m2,merge_graph G1 G2)
         od) ∧

  (ngraphOf i0 m0 (ParLoop vnm d body) =
     do
       dvs <- dvalues m0 d;
       ns <- OPT_SEQUENCE (MAP (λv.
               do
                 (i,m,g) <- ngraphOf i0 m0 (ssubst vnm v body);
                 SOME(<| reads := SET_TO_LIST (greads g);
                         writes := SET_TO_LIST (gwrites g);
                         data := DG g;
                         ident := ap1 (CONS v) i0 |>)
               od) dvs);
       assert(∀i j. i < j ∧ j < LENGTH ns ⇒ EL i ns ≁ₜ EL j ns);
       g <- SOME (FOLDR add_action emptyG ns);
       m <- nagEval g (SOME m0);
       SOME(ap2 SUC i0, m, g)
     od) ∧

  (ngraphOf i0 m0 (Par cmds) =
     do
       ns <- OPT_SEQUENCE
         (MAPi (λn c.
                 do
                   (i,m,g) <- ngraphOf i0 m0 c;
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

val _ = export_theory();
