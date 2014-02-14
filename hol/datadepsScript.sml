open HolKernel Parse boolLib bossLib;
open primitivesTheory forLoopTheory pred_setTheory
open listRangeTheory
open lcsymtacs

fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun dsimp thl = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) thl
fun csimp thl = asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss) thl

val _ = new_theory "datadeps";

val _ = set_mapped_fixity { fixity = Infixl 500, term_name = "FAPPLY",
                            tok = "<*>" }
val _ = overload_on ("FAPPLY", ``LIST_APPLY``)


val eval_def = Define`
  eval Wf Rs vf i A =
    update A (Wf i) (vf i (MAP (λf. vsub A (f i)) Rs))
`;

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

val _ = type_abbrev ("action_graph",
                     ``:'a action set # ('a action -> 'a action -> bool)``);

val wfG_def = Define`
  wfG (els,R) ⇔
      FINITE els ∧
      (∀a1 a2. R a1 a2 ⇒ touches a1 a2 ∧ a1 ∈ els ∧ a2 ∈ els) ∧
      (∀a1 a2. a1 ∈ els ∧ a2 ∈ els ∧ touches a1 a2 ∧ a1 ≠ a2 ⇒ (¬R a1 a2 ⇔ R a2 a1)) ∧
      ∀a1 a2. a1 ∈ els ∧ a2 ∈ els ∧ R⁺ a1 a2 ⇒ ¬R⁺ a2 a1
`;

val wfG_empty = store_thm(
  "wfG_empty",
  ``wfG (∅, REMPTY)``,
  simp[wfG_def]);
val _ = export_rewrites ["wfG_empty"]

val wfG_irrefl = store_thm(
  "wfG_irrefl",
  ``wfG (es,R) ∧ x ∈ es ⇒ ¬R x x``,
  simp[wfG_def] >> rpt strip_tac >>
  metis_tac[relationTheory.TC_SUBSET]);

val wfGs_pull_apart = store_thm(
  "wfGs_pull_apart",
  ``wfG (a INSERT as, R) ∧ (∀a'. a' ∈ as ⇒ ¬R a' a) ∧ a ∉ as ⇒
    wfG (as, R \\ a)``,
  simp[wfG_def] >> rw[] >>
  metis_tac[relationTheory.TC_MONOTONE, relationTheory.RDOM_DELETE_DEF]);

val _ = IndDefLib.export_rule_induction "relation.TC_STRONG_INDUCT"
val TC_in_R = store_thm(
  "TC_in_R",
  ``∀x y. R⁺ x y ⇒ (∃z. R x z) ∧ (∃z. R z y)``,
  Induct_on `R⁺ x y` >> metis_tac[]);

val wfG_WF = store_thm(
  "wfG_WF",
  ``wfG (es, R) ⇒ WF R``,
  simp[wfG_def] >> strip_tac >>
  `R = REL_RESTRICT R es`
    by (simp[REL_RESTRICT_DEF, FUN_EQ_THM, EQ_IMP_THM] >>
        metis_tac[]) >>
  first_assum (fn th => simp[FINITE_WF_noloops, Once th]) >>
  pop_assum (SUBST_ALL_TAC o SYM) >>
  simp[relationTheory.irreflexive_def] >> metis_tac[TC_in_R]);

val wfG_FINITE = store_thm(
  "wfG_FINITE",
  ``wfG (es,R) ⇒ FINITE es``,
  simp[wfG_def]);

val nonempty_wfG_has_points = store_thm(
  "nonempty_wfG_has_points",
  ``wfG (es, R) ∧ es ≠ ∅ ⇒
    ∃e. e ∈ es ∧ ∀e'. e' ∈ es ⇒ ¬R e' e``,
  rpt strip_tac >>
  `WF R` suffices_by
    (simp[relationTheory.WF_DEF, IN_DEF] >>
     pop_assum mp_tac >> simp[GSYM MEMBER_NOT_EMPTY, IN_DEF] >>
     metis_tac[]) >>
  metis_tac[wfG_WF]);

val (evalG_rules,evalG_ind,evalG_cases) = Hol_reln`
  (∀A R. evalG A (∅, R) A) ∧
  (∀a as A0 A R.
      (∀a'. a' ∈ as ⇒ ¬R a' a) ∧ a ∉ as ∧
      evalG (apply_action a A0) (as, R \\ a) A ⇒
      evalG A0 (a INSERT as, R) A)
`;

val evalG_EMPTY = store_thm(
  "evalG_EMPTY",
  ``evalG A0 (∅, R) A ⇔ A = A0``,
  simp[Once evalG_cases]);
val _ = export_rewrites ["evalG_EMPTY"]

val INSERT_11 = store_thm(
  "INSERT_11",
  ``e ∉ s1 ∧ e ∉ s2 ⇒ (e INSERT s1 = e INSERT s2 ⇔ s1 = s2)``,
  simp[EQ_IMP_THM] >> simp[EXTENSION] >> metis_tac[]);

val evalG_total = store_thm(
  "evalG_total",
  ``wfG G ⇒ ∃A'. evalG A G A'``,
  pairLib.PairCases_on `G` >> map_every qabbrev_tac [`es = G0`, `R = G1`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  map_every qid_spec_tac [`A`, `R`] >>
  Induct_on `CARD es`
  >- (simp[Once evalG_cases] >> metis_tac[CARD_EQ_0, wfG_def]) >>
  qx_gen_tac `es` >> strip_tac >>
  `es ≠ ∅` by (strip_tac >> fs[]) >>
  map_every qx_gen_tac [`R`, `A0`] >> strip_tac >>
  `∃e. e ∈ es ∧ ∀e'. e' ∈ es ⇒ ¬R e' e` by metis_tac[nonempty_wfG_has_points] >>
  `∃es0. e ∉ es0 ∧ es = e INSERT es0` by metis_tac[DECOMPOSITION] >>
  `FINITE es` by fs[wfG_def] >> rw[] >> fs[] >>
  first_x_assum (qspec_then `es0` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`R \\ e`, `apply_action e A0`] mp_tac) >>
  `wfG (es0, R \\ e)` by metis_tac[wfGs_pull_apart] >> simp[] >>
  disch_then (qx_choose_then `A0'` assume_tac) >>
  metis_tac[evalG_rules]);

val wfG_evaluate_deterministically = store_thm(
  "wfG_evaluate_deterministically",
  ``wfG G ∧ evalG A0 G A ⇒
    ∀A'. evalG A0 G A' ⇒ A' = A``,
  pairLib.PairCases_on `G` >> map_every qabbrev_tac [`es = G0`, `R = G1`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  map_every qid_spec_tac [`A0`, `A`, `R`] >>
  completeInduct_on `CARD es` >>
  qx_gen_tac `es` >>
  qmatch_rename_tac `n = CARD es ⇒ XX` ["XX"] >> strip_tac >>
  map_every qx_gen_tac [`R`, `A`, `A0`] >> strip_tac >>
  qx_gen_tac `A'` >> strip_tac >>
  full_simp_tac (srw_ss() ++ boolSimps.DNF_ss)
    [AND_IMP_INTRO, GSYM CONJ_ASSOC] >> rw[] >>
  qpat_assum `evalG A0 (es, R) A` mp_tac >>
  simp[Once evalG_cases] >>
  disch_then (DISJ_CASES_THEN2
                strip_assume_tac
                (qx_choosel_then [`e1`, `es1`] strip_assume_tac))
  >- fs[] >>
  qpat_assum `evalG XX YY A'` mp_tac >>
  simp[Once evalG_cases] >>
  disch_then (qx_choosel_then [`e2`, `es2`] strip_assume_tac) >>
  Cases_on `e2 = e1`
  >- (rw[] >>
      `es2 = es1` by metis_tac[INSERT_11] >>
      rw[] >>
      `FINITE es1` suffices_by
        (strip_tac >> fs[] >>
         metis_tac[DECIDE ``x < SUC x``, wfGs_pull_apart]) >>
      fs[wfG_def]) >>
  `e1 ∈ es2 ∧ e2 ∈ es1` by metis_tac[EXTENSION, IN_INSERT] >>
  `∃es0. es1 = e2 INSERT es0 ∧ es2 = e1 INSERT es0 ∧ e1 ∉ es0 ∧ e2 ∉ es0`
    by (`∃es0. es1 = e2 INSERT es0 ∧ e2 ∉ es0` by metis_tac[DECOMPOSITION] >>
        qexists_tac `es0` >> simp[] >> fs[] >>
        qpat_assum `XX INSERT YY INSERT ZZ = UU INSERT VV` mp_tac >>
        ONCE_REWRITE_TAC [INSERT_COMM] >> simp[INSERT_11]) >>
  rw[] >>
  `wfG (e2 INSERT es0, R \\ e1) ∧ wfG (es0, R \\ e2 \\ e1) ∧
   wfG (e1 INSERT es0, R \\ e2) ∧ wfG (es0, R \\ e1 \\ e2)`
    by metis_tac[wfGs_pull_apart, IN_INSERT, relationTheory.RDOM_DELETE_DEF] >>
  `FINITE es0` by metis_tac[wfG_FINITE] >>
  `(∃A21. evalG (apply_action e1 (apply_action e2 A0)) (es0, R \\ e2 \\ e1) A21) ∧
   ∃A12. evalG (apply_action e2 (apply_action e1 A0)) (es0, R \\ e1 \\ e2) A12`
    by metis_tac[evalG_total] >>
  `evalG (apply_action e2 A0) (e1 INSERT es0, R \\ e2) A21 ∧
   evalG (apply_action e1 A0) (e2 INSERT es0, R \\ e1) A12`
    by metis_tac[evalG_rules, IN_INSERT, relationTheory.RDOM_DELETE_DEF] >>
  `A' = A21 ∧ A = A12`
    by (conj_tac >>
        first_x_assum match_mp_tac >| [
          qexists_tac `e1 INSERT es0`,
          qexists_tac `e2 INSERT es0`
        ]>> simp[] >> metis_tac[]) >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  `R \\ e2 \\ e1 = R \\ e1 \\ e2`
    by (simp[FUN_EQ_THM, relationTheory.RDOM_DELETE_DEF] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  `apply_action e1 (apply_action e2 A0) = apply_action e2 (apply_action e1 A0)`
    suffices_by (disch_then SUBST_ALL_TAC >> first_x_assum match_mp_tac >>
                 qexists_tac `es0` >> simp[] >> metis_tac[]) >>
  `¬R e2 e1 ∧ ¬R e1 e2` by metis_tac[] >>
  `¬touches e1 e2`
    by (qpat_assum `wfG (e1 INSERT e2 INSERT es0, R)` mp_tac >>
        simp[wfG_def] >> metis_tac[]) >>
  match_mp_tac nontouching_actions_commute >> simp[]);

val add_action_def = Define`
  add_action a (As,R) =
    if a ∈ As then (As,R)
    else
      (a INSERT As,
       (λsrc tgt. R src tgt ∨
                  src = a ∧ touches a tgt ∧ tgt ∈ As))
`;

val add_action_lemma = prove(
  ``(∀a1 a2. R' a1 a2 ⇒ R a1 a2 ∨ a1 = a ∧ a2 ≠ a) ∧ (∀b. ¬R a b ∧ ¬R b a) ⇒
     ∀a1 a2. R'⁺ a1 a2 ⇒ a2 ≠ a ∧ a1 = a ∨ R⁺ a1 a2``,
  strip_tac >> Induct_on `R'⁺` >> conj_tac >- metis_tac[relationTheory.TC_SUBSET] >>
  rpt strip_tac >> simp[]
  >- metis_tac[TC_in_R]
  >- metis_tac[TC_in_R] >>
  metis_tac[relationTheory.TC_RULES]);

val wfG_add_action = store_thm(
  "wfG_add_action",
  ``wfG G ⇒ wfG (add_action a G)``,
  Cases_on `G` >>
  qmatch_rename_tac `XX ⇒ wfG (add_action a (As,R))` ["XX"] >>
  simp[add_action_def] >>
  qabbrev_tac
    `R' = (λsrc tgt. R src tgt ∨ src = a ∧ touches a tgt ∧ tgt ∈ As)`>>
  Cases_on `a ∈ As` >> simp[] >>
  `∀a1 a2. R a1 a2 ∨ a1 = a ∧ touches a a2 ∧ a2 ∈ As ⇔ R' a1 a2` by simp[Abbr`R'`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  simp[wfG_def] >> reverse (rpt strip_tac)
  >- (`∀b. ¬R a b ∧ ¬R b a` by metis_tac[] >>
      `∀a1 a2. R' a1 a2 ⇒ R a1 a2 ∨ a1 = a ∧ a2 ≠ a` by metis_tac[] >>
      pop_assum
        (fn c1 => pop_assum
           (fn c2 => assume_tac (MATCH_MP add_action_lemma (CONJ c1 c2)))) >>
      metis_tac[]) >>
  metis_tac[TC_in_R, touches_SYM]);

val mkEAction_def = Define`
  mkEAction wf rfs body i =
    <| write := wf i; reads := rfs <*> [i];
       expr := body i; iter := i |>
`;

val loop_to_graph_def = tDefine "loop_to_graph" `
  loop_to_graph (lo,hi) wf rfs body =
    if lo < hi then
      add_action (mkEAction wf rfs body lo)
                 (loop_to_graph (lo+1,hi) wf rfs body)
    else (∅, REMPTY)
` (WF_REL_TAC `measure (λp. SND (FST p) - FST (FST p))`)

val loop_to_graph_FOLDR = store_thm(
  "loop_to_graph_FOLDR",
  ``loop_to_graph (lo,hi) wf rfs body =
      FOLDR (add_action o mkEAction wf rfs body)
            (∅, REMPTY)
            [lo ..< hi]``,
  Induct_on `hi - lo` >>
  asimp[Once loop_to_graph_def,listRangeLHI_EMPTY, listRangeLHI_CONS]);

val wfG_loop_to_graph = store_thm(
  "wfG_loop_to_graph",
  ``wfG (loop_to_graph (lo, hi) wf rfs body)``,
  simp[loop_to_graph_FOLDR] >> Q.SPEC_TAC(`[lo ..< hi]`, `l`) >>
  Induct >> simp[wfG_empty, wfG_add_action]);

val eval_apply_action = store_thm(
  "eval_apply_action",
  ``eval wf rfs body i = apply_action (mkEAction wf rfs body i)``,
  simp[eval_def, apply_action_def, FUN_EQ_THM, mkEAction_def] >>
  rpt gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> Induct_on `rfs` >>
  simp[listTheory.LIST_APPLY_DEF]);

val evalG_I = store_thm(
  "evalG_I",
  ``∀A0 A G a As R.
       G = (a INSERT As,R) ∧ (∀a'. a' ∈ As ⇒ ¬R a' a) ∧ a ∉ As ∧
       evalG (apply_action a A0) (As, R \\ a) A ⇒
       evalG A0 G A``,
  simp[CONJUNCT2 evalG_rules]);

val loop_to_graph_iterations = store_thm(
  "loop_to_graph_iterations",
  ``loop_to_graph (lo,hi) wf rfs body = (As, R) ⇒
      (∀a. a ∈ As ⇒ lo ≤ a.iter ∧ a.iter < hi) ∧
      (∀a1 a2. R a1 a2 ⇒ a1 ∈ As ∧ a2 ∈ As)``,
  map_every qid_spec_tac [`As`, `R`] >>
  Induct_on `hi - lo` >> simp[Once loop_to_graph_def] >>
  rpt gen_tac >> qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> map_every qx_gen_tac [`R`, `As`] >>
  `∃As0 R0. loop_to_graph (lo + 1, hi) wf rfs body = (As0, R0)`
    by metis_tac[TypeBase.nchotomy_of ``:'a # 'b``] >>
  `n = hi - (lo + 1)` by decide_tac >>
  `(∀a. a ∈ As0 ⇒ lo + 1 ≤ a.iter ∧ a.iter < hi) ∧
   ∀a1 a2. R0 a1 a2 ⇒ a1 ∈ As0 ∧ a2 ∈ As0` by metis_tac[] >>
  simp[add_action_def] >> rw[] >> fs[mkEAction_def]
  >- (res_tac >> decide_tac)
  >- res_tac
  >- res_tac
  >- (res_tac >> decide_tac)
  >- decide_tac
  >- metis_tac[]
  >- metis_tac[]);

val loop_to_graph_correct = store_thm(
  "loop_to_graph_correct",
  ``evalG A (loop_to_graph (lo,hi) wf rfs body)
            (FOR (lo,hi) (eval wf rfs body) A)``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- simp[Once FOR_def, Once loop_to_graph_def] >>
  rpt gen_tac >>
  qmatch_rename_tac `SUC n = hi - lo ⇒ XX` ["XX"] >>
  disch_then (assume_tac o SYM) >> qx_gen_tac `A` >>
  simp[Once FOR_def, Once loop_to_graph_def, eval_apply_action] >>
  match_mp_tac evalG_I >>
  `∃As R0. loop_to_graph (lo + 1, hi) wf rfs body = (As,R0)`
    by metis_tac[TypeBase.nchotomy_of ``:'a # 'b``] >>
  simp[add_action_def] >>
  `mkEAction wf rfs body lo ∉ As`
    by (strip_tac >>
        `lo + 1 ≤ (mkEAction wf rfs body lo).iter`
          by metis_tac[loop_to_graph_iterations] >>
        full_simp_tac (srw_ss() ++ ARITH_ss) [mkEAction_def]) >>
  map_every qexists_tac [`mkEAction wf rfs body lo`, `As`] >>
  simp[] >> csimp[] >>
  `(∀a. a ∈ As ⇒ lo + 1 ≤ a.iter ∧ a.iter < hi) ∧
   ∀a1 a2. R0 a1 a2 ⇒ a1 ∈ As ∧ a2 ∈ As`
    by metis_tac[loop_to_graph_iterations] >>
  `(mkEAction wf rfs body lo).iter = lo ∧ ¬(lo + 1 ≤ lo)`
    by simp[mkEAction_def] >>
  conj_tac >- metis_tac[] >>
  qmatch_abbrev_tac `
    evalG AA (As, RR \\ act) (FOR (lo + 1, hi) (eval wf rfs body) AA)
  ` >>
  `n = hi - (lo + 1)` by decide_tac >>
  `RR \\ act = R0` suffices_by metis_tac[] >>
  qunabbrev_tac `RR` >> csimp[FUN_EQ_THM] >> metis_tac[]);

val RIMAGE_DEF = new_definition(
  "RIMAGE_DEF",
  ``RIMAGE f R x y <=> ?a b. (x = f a) /\ (y = f b) /\ R a b``);

val imap_def = Define`
  imap (f:'a action -> num) ((As,R):'a action_graph) =
     (IMAGE (λa. a with iter := f a) As,
      RIMAGE (λa. a with iter := f a) R)
`;

val imap_irrelevance = store_thm(
  "imap_irrelevance",
  ``∀A0 AG A.
      evalG A0 AG A ⇒
      wfG AG ⇒
        ∀f Is. INJ f (FST AG) Is ⇒ evalG A0 (imap f AG) A``,
  Induct_on `evalG` >> simp[imap_def] >> rpt strip_tac >>
  match_mp_tac (CONJUNCT2 evalG_rules) >> simp[RIMAGE_DEF] >>
  `∀a1 a2. R a1 a2 ⇒ (a1 = a ∨ a1 ∈ as) ∧ (a2 = a ∨ a2 ∈ as)`
     by metis_tac[wfG_def, IN_INSERT] >>
  `∀a1 a2. (a1 = a ∨ a1 ∈ as) ∧ (a2 = a ∨ a2 ∈ as) ⇒
           (a1 with iter := f a1 = a2 with iter := f a2 ⇔
            a1 = a2)`
    by (rpt gen_tac >> disch_then assume_tac >>
        simp[Once (theorem "action_component_equality"), EQ_IMP_THM] >>
        qpat_assum `INJ f XX YY` mp_tac >>
        REWRITE_TAC[INJ_DEF, IN_INSERT] >> metis_tac[]) >>
  rpt conj_tac >| [
    dsimp[] >> map_every qx_gen_tac [`a1`, `a1'`, `a'`] >> strip_tac >>
    Cases_on `R a1' a'` >> simp[] >>
    Cases_on `a' = a`
    >- (rw[] >> `a1' ∉ as` by metis_tac[] >> `a1' = a` by metis_tac[] >>
        metis_tac[wfG_irrefl, IN_INSERT]) >>
    `a' ∈ as` by metis_tac[] >> simp[],
    qx_gen_tac `a2` >> Cases_on `a2 ∈ as` >> simp[] >> metis_tac[],
    `apply_action (a with iter := f a) A0 = apply_action a A0`
      by simp[apply_action_def] >> simp[] >>
    `RIMAGE (λa. a with iter := f a) R \\ (a with iter := f a) =
     RIMAGE (λa. a with iter := f a) (R \\ a)`
      by (simp[FUN_EQ_THM, RIMAGE_DEF] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >> imp_res_tac wfGs_pull_apart >> fs[] >>
    first_x_assum match_mp_tac >> qexists_tac `Is` >>
    qpat_assum `INJ f XX YY` mp_tac >> metis_tac[INJ_INSERT]
  ]);

val example_t =
  ``FOR (0,N)
      (eval (vsub (f : num mvector))
            [(λi. i + 1); vsub (h : num mvector)]
            (λi rds. EL 0 rds + EL 1 rds + 1))``;

val computation =
    EVAL ``let N = 5 in
           let f = ((λi. EL i [4;3;2;1;0]), 5) in
           let h = ((λi. EL i [0;1;1;2;3]), 5) in
             ^example_t ((λi. EL i [0;0;0;0;0;0]), 6)``


(* C original:
int N = 5;
int A[6] = {0};
int f[5] = {4,3,2,1,0};
int h[5] = {0,1,1,2,3};

for (int i= 0; i < N; i++)
  A[f[i]] = A[i+1] + A [h[i]];


*)

val ddepR_def = Define`
  ddepR wf rfs i0 i ⇔
    i0 < i ∧ (wf i0 = wf i ∨
              MEM (wf i0) (rfs <*> [i]) ∨
              MEM (wf i) (rfs <*> [i0]))
`;

val ddepR_irreflexive = store_thm(
  "ddepR_irreflexive",
  ``∀i. ¬ddepR wf rfs i i``,
  rw[ddepR_def]);
val _ = export_rewrites ["ddepR_irreflexive"]

val ddepR_TC_LT = store_thm(
  "ddepR_TC_LT",
  ``∀i j. (ddepR wf rfs)⁺ i j ⇒ i < j``,
  ho_match_mp_tac relationTheory.TC_INDUCT >>
  rw[ddepR_def] >> decide_tac);

val ddepR_acyclic = store_thm(
  "ddepR_acyclic",
  ``∀i. ¬(ddepR wf rfs)⁺ i i``,
  rpt strip_tac >> imp_res_tac ddepR_TC_LT >> fs[]);
val _ = export_rewrites ["ddepR_acyclic"]

val vsz_eval = store_thm(
  "vsz_eval",
  ``vsz (eval wf rfs body i A) = vsz A``,
  simp[eval_def]);
val _ = export_rewrites ["vsz_eval"]

val vsz_eval_FOR = store_thm(
  "vsz_eval_FOR",
  ``vsz (FOR (lo,hi) (eval wf rfs body) A) = vsz A``,
  DEEP_INTRO_TAC FOR_RULE >> qexists_tac `λi A'. vsz A' = vsz A` >>
  simp[]);
val _ = export_rewrites ["vsz_eval_FOR"]

val vsub_eval_out_range_FOR = store_thm(
  "vsub_eval_out_range_FOR",
  ``(∀j. lo ≤ j ∧ j < hi ⇒ wf j ≠ i) ⇒ FOR (lo,hi) (eval wf rfs body) A ' i = A ' i``,
  strip_tac >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λj a. a ' i = A ' i` >> simp[eval_def] >>
  simp[update_sub]);

(* now convinced that this approach, based on what was done for
"simple" loops, can't work because it's hard to imagine using it
anything about the contents of the array part-way through the loop. In
the simple case, a given index had either been written or had not.
Here, depending on the wf array/function, an array cell may be written
multiple times.

val correct0 = prove(
  ``BIJ δ (count N) (count N) ∧ Abbrev (γ = LINV δ (count N)) ∧
    (∀j. j < N ⇒ wf j < N) ∧
    (final = FOR (0,N) (eval wf rfs body) A1) ∧
    (∀i0 i. ddepR wf rfs i0 i ==> δ i0 < δ i) ⇒
    ∀m n A2.
      (vsz A1 = vsz A2) ∧ N ≤ vsz A1 ∧
      (m = N - n) ∧ n ≤ N ∧
      (∀i. A2 ' i = if i ∈ IMAGE δ (count n) then vsub final i
                    else vsub A1 i)
     ⇒
      (FOR (n, N) (eval (wf o γ) (MAP (λf. f o γ) rfs) body) A2 = final)``,
  strip_tac >> Induct >| [
    rpt strip_tac >> `N = n` by decide_tac >>
    qpat_assum `0 = N - n` kall_tac >>
    srw_tac[ARITH_ss][] >>
    srw_tac[ARITH_ss][vector_EQ] >>
    Cases_on `i < N`
    >- (`∃j. j < N ∧ (i = δ j)`
          by metis_tac[BIJ_DEF, IN_COUNT, SURJ_DEF] >>
        rw[] >> metis_tac[]) >>
    metis_tac[vsub_eval_out_range_FOR],

    rpt strip_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    srw_tac[ARITH_ss][] >> fs[AND_IMP_INTRO] >>
    first_x_assum match_mp_tac >> asimp[] >>
    `n < N` by decide_tac >>
    qx_gen_tac `i` >>
    `∀i. i < N ⇒ γ i < N`
      by (simp[Abbr`γ`] >> imp_res_tac BIJ_LINV_BIJ >>
          metis_tac[BIJ_DEF, SURJ_DEF, IN_COUNT]) >>
    reverse (Cases_on `i < N`)
    >- (`FOR (0,N) (eval wf rfs body) A1 ' i = A1 ' i`
          by metis_tac[vsub_eval_out_range_FOR] >>
        simp[] >>
        `A2 ' i = A1 ' i` by simp[] >>
        `i ≠ wf (γ n)` suffices_by
          simp[eval_def, update_sub] >>
        metis_tac[]) >>
    Cases_on `i = wf (γ n)`


    simp_tac (srw_ss()) [eval_def]

Cases_on `i = n` >| [
      pop_assum SUBST_ALL_TAC >>
      `n < N` by decide_tac >>
      `δ n < N` by metis_tac[BIJ_DEF, IN_COUNT, SURJ_DEF] >>
      simp_tac (srw_ss())[eval_def]
*)

(* val same_graphs = prove(
  ``(∀i0 i. ddepR wf rfs i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N) ⇒
    loop_to_graph (0,N) (wf o γ) (MAP (λf. f o γ) rds) body =
      imap (λa. δ a.iter) (loop_to_graph (0,N) wf rds body)``,
  strip_tac >> SIMP_TAC (srw_ss()) [Once loop_to_graph_def, SimpLHS] >>
  SIMP_TAC (srw_ss()) [Once loop_to_graph_def, SimpRHS] >>
  pop_assum (assume_tac o SYM) >>
  Cases_on `0 < N` >> simp[]
*)

(*
val correctness = store_thm(
  "correctness",
  ``(∀i0 i. ddepR wf rfs i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N)
  ==>
    FOR (0,N) (eval wf rfs body) =
    FOR (0,N) (eval (wf o γ)
                    (MAP (λf. f o γ) rds)
                    body)``



*)
val _ = export_theory();
