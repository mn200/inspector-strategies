open HolKernel Parse boolLib bossLib;

open actionTheory actionGraphTheory datadepsTheory
open pred_setTheory listTheory sortingTheory relationTheory
open indexedListsTheory

open lcsymtacs

fun dsimp thl = ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) thl

val _ = new_theory "wavefronts";

val total_LE = store_thm(
  "total_LE",
  ``total (<=)``,
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [total_def]);
val _ = export_rewrites ["total_LE"]

val transitive_LE = store_thm(
  "transitive_LE",
  ``transitive (<=)``,
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [transitive_def])
val _ = export_rewrites ["transitive_LE"]

val waveR_def = Define`
  waveR G = inv_image (inv_image (<=) (wave G) LEX (<=)) (λe. (e,e))
`;

val waveR_transitive = store_thm(
  "waveR_transitive",
  ``transitive (waveR G)``,
  simp[waveR_def]);
val _ = export_rewrites ["waveR_transitive"]

val GENLIST_EQ_NIL = store_thm(
  "GENLIST_EQ_NIL",
  ``(GENLIST f n = [] ⇔ n = 0) ∧
    ([] = GENLIST f n ⇔ n = 0)``,
  Cases_on `n` >> simp[GENLIST_CONS]);

val GENLIST_EQ_CONS = store_thm(
  "GENLIST_EQ_CONS",
  ``GENLIST f n = h::t ⇔ ∃m. n = SUC m ∧ h = f 0 ∧ t = GENLIST (f o SUC) m``,
  Cases_on `n` >> simp[GENLIST_CONS] >> metis_tac[]);

val lift_splitAtPki_RAND = store_thm(
  "lift_splitAtPki_RAND",
  ``∀P k. f (splitAtPki P k l) = splitAtPki P ((o) f o k) l``,
  Induct_on `l` >> simp[splitAtPki_DEF] >>
  map_every qx_gen_tac [`h`, `P`, `k`] >>
  Cases_on `P 0 h` >> simp[combinTheory.o_DEF]);

val lift_splitAtPki_RATOR = store_thm(
  "lift_splitAtPki_RATOR",
  ``∀P k. splitAtPki P k l x =
          splitAtPki P (combin$C (combin$C o k) x) l``,
  Induct_on `l` >> simp[splitAtPki_DEF] >> rw[combinTheory.C_DEF]);

val splitAtPki_l1 = prove(
  ``splitAtPki P (λl1 l2. f l1) l = f (splitAtPki P (λl1 l2. l1) l)``,
  CONV_TAC (RAND_CONV (REWR_CONV lift_splitAtPki_RAND)) >>
  simp[combinTheory.o_DEF]);

val BIJ_CONG = store_thm(
  "BIJ_CONG",
  ``s1 = s1' ⇒ s2 = s2' ⇒ (∀x. x ∈ s1' ⇒ f x = f' x) ⇒
    (BIJ f s1 s2 ⇔ BIJ f' s1' s2')``,
  SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss)
           [BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM]);

val PERM_BIJ = store_thm(
  "PERM_BIJ",
  ``∀l1 l2. PERM l1 l2 ∧ ALL_DISTINCT l1 ⇒
            BIJ (λx. EL (findi x l1) l2) (set l1) (set l1)``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] >>
  `∀x. PRE (x + 1) = x` by decide_tac >>
  `∀x. PRE (x + 2) = x + 1` by decide_tac >>
  Induct_on `PERM l1 l2` >> simp[BIJ_EMPTY] >> rpt strip_tac
  >- (`∀y. y ∈ set l1 ⇒ y <> x` by metis_tac[] >>
      simp[BIJ_INSERT, findi_def, DELETE_INSERT, DELETE_NON_ELEMENT_RWT,
           Cong BIJ_CONG, rich_listTheory.EL_CONS])
  >- (`∀z. z ∈ set l1 ⇒ z <> x ∧ z <> y` by metis_tac[] >>
      simp[BIJ_INSERT, findi_def, DELETE_INSERT, DELETE_NON_ELEMENT_RWT,
           Cong BIJ_CONG, rich_listTheory.EL_CONS]) >>
  `ALL_DISTINCT l1'` by metis_tac [ALL_DISTINCT_PERM] >> fs[] >>
  `set l1' = set l1 ∧ LENGTH l1' = LENGTH l1`
    by metis_tac [PERM_LIST_TO_SET, PERM_LENGTH] >> fs[] >>
  `∀x. x ∈ set l1 ⇒
       EL (findi (EL (findi x l1) l1') l1') l2 = EL (findi x l1) l2`
    by simp[findi_EL, MEM_findi] >>
  `BIJ ((λx. EL (findi x l1') l2) o (λx. EL (findi x l1) l1'))
       (set l1) (set l1)`
    by metis_tac [BIJ_COMPOSE] >>
  pop_assum mp_tac >> simp[Cong BIJ_CONG])

val wavesort_sorted = store_thm(
  "wavesort_sorted",
  ``SORTED (waveR G) (QSORT (waveR G) l)``,
  match_mp_tac QSORT_SORTED >> simp[waveR_def]);

val set_listRangeLHI = store_thm(
  "set_listRangeLHI",
  ``set [lo ..< hi] = count hi DIFF count lo``,
  simp[EXTENSION]);

val MAX_SET_LT = store_thm(
  "MAX_SET_LT",
  ``FINITE s ∧ MAX_SET s < x ⇒ ∀e. e ∈ s ⇒ e < x``,
  `∀s. FINITE s ⇒ MAX_SET s < x ⇒ ∀e. e ∈ s ⇒ e < x`
    suffices_by metis_tac[] >>
  Induct_on `FINITE s` >> dsimp[MAX_SET_THM]);

val LT_MAX_SET = store_thm(
  "LT_MAX_SET",
  ``FINITE s ∧ (∃e. e ∈ s ∧ x < e) ⇒ x < MAX_SET s``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> qid_spec_tac `s` >>
  Induct_on `FINITE s` >> dsimp[MAX_SET_THM] >> metis_tac[]);

val action_ident_mkEAction = store_thm(
  "action_ident_mkEAction",
  ``action_ident o mkEAction wf rds body = I``,
  simp[FUN_EQ_THM]);

val idents_FOLD_add_action = store_thm(
  "idents_FOLD_add_action",
  ``idents (FOLDR (add_action o mkEAction wf rds body) G l) =
    idents G ∪ set l``,
  Induct_on `l` >> simp[EXTENSION] >> metis_tac[]);

val IN_idents_loop_to_graph = store_thm(
  "IN_idents_loop_to_graph",
  ``i ∈ idents (loop_to_graph (lo,hi) wf rds body) ⇔ lo ≤ i ∧ i < hi``,
  dsimp[loop_to_graph_FOLDR, idents_FOLD_add_action])

val FOLD_add_action_fmap = store_thm(
  "FOLD_add_action_fmap",
  ``i ∈ set l ⇒
    FOLDR (add_action o mkEAction wf rds body) emptyG l ' i =
    mkEAction wf rds body i``,
  Induct_on `l` >> simp[fmap_add_action] >> qx_gen_tac `h` >>
  Cases_on `h = i` >> simp[] >> Cases_on `MEM i l` >> simp[] >>
  dsimp[idents_FOLD_add_action]);

val ua = REWRITE_RULE [markerTheory.Abbrev_def]

val ddepR_wave = store_thm(
  "ddepR_wave",
  ``ddepR wf rds i j ∧ lo ≤ i ∧ j < hi ∧
    Abbrev(G = loop_to_graph (lo,hi) wf rds body) ⇒
    wave G i < wave G j``,
  strip_tac >> simp[SimpR ``$<``, Once wave_thm] >>
  match_mp_tac LT_MAX_SET >> conj_tac
  >- (`{wave G k + 1 | k | k -<G>#-> j} =
       IMAGE (λk. wave G k + 1) { k | k -<G>#-> j}`
        by simp[EXTENSION] >> pop_assum SUBST_ALL_TAC >>
      match_mp_tac IMAGE_FINITE >> match_mp_tac SUBSET_FINITE_I >>
      qexists_tac `idents G` >>
      simp[idents_thm, SUBSET_DEF, ilink_def]) >>
  dsimp[] >> qexists_tac `i` >> simp[ilink_def] >>
  `idents G = { k | lo ≤ k ∧ k < hi}`
     by simp[EXTENSION, IN_idents_loop_to_graph, Abbr`G`] >>
  `i < j` by fs[ddepR_def] >>
  simp[] >> simp[Abbr`G`, loop_to_graph_FOLDR,
                 FOLD_add_action_edges_ALL_DISTINCT] >>
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
    [listRangeTheory.EL_listRangeLHI] >>
  map_every qexists_tac [`i - lo`, `j - lo`] >>
  simp[FOLD_add_action_fmap] >>
  fs[ddepR_def, touches_def, mkEAction_def]);

val ua' = let
  val th = prove(``Abbrev(x = y) ⇔ (y = x)``,
                 simp[markerTheory.Abbrev_def, EQ_SYM_EQ])
in
  REWRITE_RULE [th]
end

val wavesort_correctness = save_thm(
  "wavesort_correctness",
  (ua' o prove)(
  ``Abbrev(l1 = [0 ..< N]) ∧ Abbrev(G = loop_to_graph (0,N) wf rds body) ∧
    Abbrev(l2 = QSORT (waveR G) l1) ∧
    Abbrev(f = λn. EL (findi n l2) l1) ⇒
    (∀i0 i. i < N ∧ ddepR wf rds i0 i ⇒ f i0 < f i) ∧
    BIJ f (count N) (count N)``,
  strip_tac >>
  `PERM l1 l2 ∧ PERM l2 l1` by metis_tac[QSORT_PERM, PERM_SYM] >>
  reverse conj_tac
  >- (`count N = set l1` by simp[Abbr`l1`, set_listRangeLHI] >>
      `set l1 = set l2` by metis_tac[PERM_LIST_TO_SET] >>
      simp[Abbr`f`] >> match_mp_tac PERM_BIJ >>
      `ALL_DISTINCT l1` by simp[Abbr`l1`] >>
      metis_tac[ALL_DISTINCT_PERM]) >>
  `∀i. i < N ⇒ EL i l1 = i`
    by simp[Abbr`l1`, listRangeTheory.EL_listRangeLHI] >>
  `LENGTH l1 = N` by simp[Abbr`l1`] >>
  `LENGTH l2 = N` by metis_tac[PERM_LENGTH] >>
  `∀i. i < N ⇒ MEM i l1` by simp[Abbr`l1`] >>
  `∀i. i < N ⇒ MEM i l2` by metis_tac[MEM_PERM] >>
  `∀i. i < N ⇒ findi i l2 < N` by metis_tac[MEM_findi] >>
  simp[Abbr`f`] >> rpt strip_tac >>
  `i0 < i ∧ i0 < N` by fs[ddepR_def] >> simp[] >>
  `wave G i0 < wave G i` by metis_tac[ua ddepR_wave, DECIDE ``0 ≤ n``] >>
  `findi i0 l2 ≠ findi i l2` by metis_tac[EL_findi, DECIDE ``~(x < x)``] >>
  `¬(findi i l2 < findi i0 l2)` suffices_by decide_tac >> strip_tac >>
  `SORTED (waveR G) l2` by metis_tac [wavesort_sorted] >>
  qspec_then `l2` SUBST_ALL_TAC (MATCH_MP SORTED_EL_LESS waveR_transitive) >>
  pop_assum (qspecl_then [`findi i l2`, `findi i0 l2`] mp_tac) >>
  simp[EL_findi] >>
  simp[waveR_def, relationTheory.inv_image_def, pairTheory.LEX_DEF]));

val _ = export_theory();
