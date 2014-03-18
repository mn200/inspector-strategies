open HolKernel Parse boolLib bossLib;

open actionGraphTheory datadepsTheory
open pred_setTheory listTheory sortingTheory relationTheory

open lcsymtacs

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

val findi_def = Define`
  findi x [] = 0 ∧
  findi x (h::t) = if x = h then 0 else 1 + findi x t
`;

val MEM_findi = prove(
  ``MEM x l ⇒ findi x l < LENGTH l``,
  Induct_on `l` >> simp[findi_def] >>
  rw[arithmeticTheory.ADD1, arithmeticTheory.ZERO_LESS_ADD]);

val BIJ_CONG = store_thm(
  "BIJ_CONG",
  ``s1 = s1' ⇒ s2 = s2' ⇒ (∀x. x ∈ s1' ⇒ f x = f' x) ⇒
    (BIJ f s1 s2 ⇔ BIJ f' s1' s2')``,
  SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss)
           [BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM]);

val findi_EL = store_thm(
  "findi_EL",
  ``∀l n. n < LENGTH l ∧ ALL_DISTINCT l ⇒ findi (EL n l) l = n``,
  Induct >> simp[] >> map_every qx_gen_tac [`h`, `n`] >> strip_tac >>
  Cases_on `n` >> simp[findi_def] >> rw[arithmeticTheory.ADD1] >>
  fs[] >> metis_tac[MEM_EL]);

val PERM_BIJ = store_thm(
  "PERM_BIJ",
  ``∀l1 l2. PERM l1 l2 ⇒ ALL_DISTINCT l1 ⇒
            BIJ (λx. EL (findi x l1) l2) (set l1) (set l1)``,
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

(*
val SORTED_SEPARATED_ELEMENTS = store_thm(
  "SORTED_SEPARATED_ELEMENTS",
  ``transitive R ∧ SORTED R l ⇒
    ∀i j. i < j ∧ j < LENGTH l ⇒ R (EL i l) (EL j l)``,
  Induct_on `l` >> simp[] >> qx_gen_tac `h` >>
  Cases_on `l` >> simp[SORTED_DEF]
*)


val _ = export_theory();
