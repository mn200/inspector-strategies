open HolKernel Parse boolLib bossLib;

open lcsymtacs listTheory

val _ = new_theory "indexedLists";

val _ = ParseExtras.tight_equality()

val MAPi_def = Define`
  (MAPi f [] = []) ∧
  (MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t)
`;
val _ = export_rewrites ["MAPi_def"]

val LT_SUC = store_thm(
  "LT_SUC",
  ``n < SUC m ⇔ n = 0 ∨ ∃n0. n = SUC n0 ∧ n0 < m``,
  simp[EQ_IMP_THM] >> Cases_on `n` >> simp[]);

val MEM_MAPi = store_thm(
  "MEM_MAPi",
  ``∀x f l. MEM x (MAPi f l) ⇔
            ∃n. n < LENGTH l ∧ x = f n (EL n l)``,
  Induct_on `l` >> simp[] >> pop_assum kall_tac >>
  dsimp[EQ_IMP_THM, LT_SUC] >> metis_tac[]);

val MAPi_CONG = store_thm(
  "MAPi_CONG",
  ``∀l1 l2 f1 f2.
      l1 = l2 ∧ (∀x n. MEM x l2 ∧ n < LENGTH l2 ⇒ f1 n x = f2 n x) ⇒
      MAPi f1 l1 = MAPi f2 l2``,
  Induct_on `l1` >> dsimp[LT_SUC]);
val _ = DefnBase.export_cong "MAPi_CONG"

val MAPi_CONG' = store_thm(
  "MAPi_CONG'",
  ``l1 = l2 ⇒ (∀x n. (x = EL n l2) ⇒ n < LENGTH l2 ⇒ f1 n x = f2 n x) ⇒
    MAPi f1 l1 = MAPi f2 l2``,
  map_every qid_spec_tac [`f1`, `f2`, `l2`] >> Induct_on `l1` >>
  dsimp[LT_SUC]);

val LENGTH_MAPi = store_thm(
  "LENGTH_MAPi[simp]",
  ``∀f l. LENGTH (MAPi f l) = LENGTH l``,
  Induct_on `l` >> simp[]);

val MAP_MAPi = store_thm(
  "MAP_MAPi[simp]",
  ``∀f g l. MAP f (MAPi g l) = MAPi ((o) f o g) l``,
  Induct_on `l` >> simp[]);

val EL_MAPi = store_thm(
  "EL_MAPi[simp]",
  ``∀f n l. n < LENGTH l ⇒ EL n (MAPi f l) = f n (EL n l)``,
  Induct_on `l` >> simp[] >> dsimp[LT_SUC]);

val MAPi_APPEND = store_thm(
  "MAPi_APPEND",
  ``∀l1 l2 f. MAPi f (l1 ++ l2) = MAPi f l1 ++ MAPi (f o (+) (LENGTH l1)) l2``,
  Induct >> simp[] >> rpt gen_tac >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]);

val MAPi_GENLIST = store_thm(
  "MAPi_GENLIST",
  ``∀l f. MAPi f l = GENLIST (S f (combin$C EL l)) (LENGTH l)``,
  Induct >> simp[GENLIST_CONS] >> rpt gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[FUN_EQ_THM]);

val GENLIST_CONG = store_thm(
  "GENLIST_CONG",
  ``(∀m. m < n ⇒ f1 m = f2 m) ⇒ GENLIST f1 n = GENLIST f2 n``,
  map_every qid_spec_tac [`f1`, `f2`] >> Induct_on `n` >>
  simp[GENLIST_CONS]);

val FOLDRi_def = Define`
  (FOLDRi f a [] = a) ∧
  (FOLDRi f a (h::t) = f 0 h (FOLDRi (f o SUC) a t))`
val _ = export_rewrites ["FOLDRi_def"]

val FOLDR_MAPi = store_thm(
  "FOLDR_MAPi",
  ``∀f g a l. FOLDR f a (MAPi g l) = FOLDRi ($o f o g) a l``,
  Induct_on `l` >> simp[MAPi_def]);

val FOLDRi_APPEND = store_thm(
  "FOLDRi_APPEND",
  ``∀f. FOLDRi f a (l1 ++ l2) = FOLDRi f (FOLDRi (f o $+ (LENGTH l1)) a l2) l1``,
  Induct_on `l1` >> simp[]
  >- (gen_tac >> `f o $+ 0 = f` suffices_by simp[] >> simp[FUN_EQ_THM]) >>
  rpt gen_tac >>
  `f o SUC o $+ (LENGTH l1) = f o $+ (SUC (LENGTH l1))` suffices_by simp[] >>
  simp[FUN_EQ_THM, arithmeticTheory.ADD_CLAUSES]);

val FOLDRi_CONG = store_thm(
  "FOLDRi_CONG",
  ``l1 = l2 ⇒
    (∀n e a. n < LENGTH l2 ⇒ MEM e l2 ⇒ f1 n e a = f2 n e a) ⇒
    a1 = a2 ⇒
    FOLDRi f1 a1 l1 = FOLDRi f2 a2 l2``,
  disch_then SUBST_ALL_TAC >> strip_tac >> disch_then SUBST_ALL_TAC >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`f1`, `f2`] >>
  Induct_on `l2` >> simp[] >> dsimp[LT_SUC] >> rpt strip_tac >>
  AP_TERM_TAC >> first_x_assum match_mp_tac >> simp[]);

val FOLDRi_CONG' = store_thm(
  "FOLDRi_CONG'",
  ``l1 = l2 ∧ (∀n a. n < LENGTH l2 ⇒ f1 n (EL n l2) a = f2 n (EL n l2) a) ∧
    a1 = a2 ⇒
    FOLDRi f1 a1 l1 = FOLDRi f2 a2 l2``,
  strip_tac >> rw[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`f1`, `f2`] >> Induct_on `l1` >>
  dsimp[LT_SUC] >> rpt strip_tac >> AP_TERM_TAC >>
  first_x_assum match_mp_tac >> simp[]);

val findi_def = Define`
  findi x [] = 0 ∧
  findi x (h::t) = if x = h then 0 else 1 + findi x t
`;

val MEM_findi = store_thm(
  "MEM_findi",
  ``MEM x l ⇒ findi x l < LENGTH l``,
  Induct_on `l` >> simp[findi_def] >>
  rw[arithmeticTheory.ADD1, arithmeticTheory.ZERO_LESS_ADD]);

val findi_EL = store_thm(
  "findi_EL",
  ``∀l n. n < LENGTH l ∧ ALL_DISTINCT l ⇒ findi (EL n l) l = n``,
  Induct >> simp[] >> map_every qx_gen_tac [`h`, `n`] >> strip_tac >>
  Cases_on `n` >> simp[findi_def] >> rw[arithmeticTheory.ADD1] >>
  fs[] >> metis_tac[MEM_EL]);

val EL_findi = store_thm(
  "EL_findi",
  ``∀l x. MEM x l ⇒ EL (findi x l) l = x``,
  Induct_on`l` >> rw[findi_def] >> simp[DECIDE ``1 + x = SUC x``]);

val delN_def = Define`
  delN i [] = [] ∧
  delN i (h::t) = if i = 0 then t
                  else h::delN (i - 1) t
`;

val delN_shortens = store_thm(
  "delN_shortens",
  ``∀l i. i < LENGTH l ⇒ LENGTH (delN i l) = LENGTH l - 1``,
  Induct >> dsimp[delN_def, LT_SUC]);

val EL_delN_BEFORE = store_thm(
  "EL_delN_BEFORE",
  ``∀l i j. i < j ∧ j < LENGTH l ⇒ EL i (delN j l) = EL i l``,
  Induct >> simp[delN_def] >> map_every qx_gen_tac [`h`, `i`, `j`] >>
  Cases_on `i` >> simp[])

val EL_delN_AFTER = store_thm(
  "EL_delN_AFTER",
  ``∀l i j. j ≤ i ∧ i + 1 < LENGTH l ⇒ (EL i (delN j l) = EL (i + 1) l)``,
  Induct >> simp[delN_def] >> rw[]
  >- simp[GSYM arithmeticTheory.ADD1] >>
  `∃i0. i = SUC i0` by (Cases_on `i` >> fs[]) >> rw[] >>
  fs[arithmeticTheory.ADD_CLAUSES] >> simp[]);

val fupdLast_def = Define`
  (fupdLast f [] = []) /\
  (fupdLast f [h] = [f h]) /\
  (fupdLast f (h::t) = h::fupdLast f t)
`;
val _ = export_rewrites ["fupdLast_def"]

val fupdLast_EQ_NIL = store_thm(
  "fupdLast_EQ_NIL[simp]",
  ``(fupdLast f x = [] ⇔ x = []) ∧
    ([] = fupdLast f x ⇔ x = [])``,
  Cases_on `x` >> simp[] >> Cases_on `t` >> simp[]);

val fupdLast_FRONT_LAST = store_thm(
  "fupdLast_FRONT_LAST",
  ``fupdLast f l = if l = [] then []
                  else FRONT l ++ [f (LAST l)]``,
  Induct_on `l` >> simp[] >> Cases_on `l` >> simp[]);

val _ = export_theory();
