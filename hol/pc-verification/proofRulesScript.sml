open HolKernel Parse boolLib bossLib;

open optionTheory pairTheory listTheory rich_listTheory
open indexedListsTheory listExtrasTheory hidagTheory PseudoCTheory
open PseudoCHDAGTheory

open lcsymtacs monadsyntax

val _ = new_theory "proofRules";

val _ = set_trace "Goalstack.print_goal_at_top" 0

(* cSOMEP because it's a conjunctive thing; the value has to be a SOME,
   and the value under the SOME has to satisfy the predicate.
   Contrast iSOMEP (later), which is implicative *)
val cSOMEP_def = Define`
  ((cSOMEP) P NONE ⇔ F) ∧
  ((cSOMEP) P (SOME x) ⇔ P x)
`
val _ = export_rewrites ["cSOMEP_def"]
val _ = set_fixity "cSOMEP" Binder
val _ = augment_srw_ss [intSimps.OMEGA_ss]

val cSOMEP_OPTION_BIND_I = store_thm(
  "cSOMEP_OPTION_BIND_I",
  ``∀P R f v. $cSOMEP R v ∧ (∀z. R z ⇒ $cSOMEP P (f z)) ⇒
              $cSOMEP P (OPTION_BIND v f)``,
  rpt gen_tac >> Cases_on `v` >> simp[]);

val cSOMEP_EQN = store_thm(
  "cSOMEP_EQN",
  ``$cSOMEP P v ⇔ ∃x. v = SOME x ∧ P x``,
  Cases_on `v` >> simp[]);

val Num_EQ_num = store_thm(
  "Num_EQ_num",
  ``0 ≤ i ⇒ (Num i = n ⇔ i = &n) ∧ (n = Num i ⇔ i = &n)``,
  strip_tac >> simp[integerTheory.Num] >> SELECT_ELIM_TAC >> simp[] >>
  metis_tac [integerTheory.NUM_POSINT_EXISTS]);

val Num_LT_num = store_thm(
  "Num_LT_num",
  ``0 ≤ i ⇒ (Num i < n ⇔ i < &n) ∧ (n < Num i ⇔ &n < i)``,
  strip_tac >> simp[integerTheory.Num] >> SELECT_ELIM_TAC >> simp[] >>
  metis_tac [integerTheory.NUM_POSINT_EXISTS]);

val total_for_rule = store_thm(
  "total_for_rule",
  ``evalexpr m0 lo_e = Int lo ∧ evalexpr m0 hi_e = Int hi ∧
    Inv lo (m0, ε) ∧
    (∀m g i. lo ≤ i ∧ i < hi ∧ Inv i (m,g) ⇒
             (cSOMEP (m',sg).  Inv (i + 1) (m', g ⊕ (HG sg <+ ε)))
               (graphOf (Int i :: lab) m (ssubst v (Int i) s))) ∧
    (∀m g. Inv (int_max lo hi) (m, g) ⇒
           P (m, HD (addLabel lab (domreadAction () m0 (D lo_e hi_e))) <+ g)) ⇒
      (cSOMEP) P (graphOf lab m0 (ForLoop v (D lo_e hi_e) s))``,
  simp[graphOf_def, dvalues_def, FOLDL_FOLDR_REVERSE, MAP_GENLIST,
       REVERSE_GENLIST] >>
  reverse (Cases_on `lo ≤ hi`) >> simp[]
  >- (rpt strip_tac >> `int_max lo hi = lo` by simp[] >>
      first_x_assum match_mp_tac >> simp[]) >>
  `int_max lo hi = hi` by simp[] >> simp[] >>
  simp[DECIDE ``PRE n - m = n - (m + 1)``] >>
  qabbrev_tac `sz = Num (hi - lo)` >>
  `∀m. m < sz ⇒ &(sz - (m + 1)) + lo = hi - &(m + 1)`
    by simp[int_arithTheory.INT_NUM_SUB, Abbr`sz`] >>
  pop_assum (fn th => simp[th, Cong GENLIST_CONG]) >> rpt strip_tac >>
  qunabbrev_tac `sz` >>
  match_mp_tac cSOMEP_OPTION_BIND_I >> qexists_tac `Inv hi` >>
  simp[FORALL_PROD] >>
  map_every (fn q => Q.UNDISCH_THEN q kall_tac) [
    `evalexpr m0 lo_e = Int lo`, `evalexpr m0 hi_e = Int hi`
  ] >>
  qpat_assum `∀m g. Inv hi (m,g) ==> X` kall_tac >>
  Induct_on `Num (hi - lo)` >> simp[] >> rpt strip_tac
  >- fs[Num_EQ_num] >>
  qcase_tac `SUC sz = Num (hi - lo)` >>
  fs[Num_EQ_num, arithmeticTheory.ADD1, GSYM integerTheory.INT_ADD] >>
  simp[integerTheory.INT_ADD, GENLIST_APPEND] >>
  match_mp_tac cSOMEP_OPTION_BIND_I >>
  qexists_tac `Inv (hi - 1)` >> simp[FORALL_PROD] >> reverse conj_tac
  >- (qx_genl_tac [`m1`, `g1`] >>
      first_x_assum (qspecl_then [`m1`, `g1`, `hi - 1`] mp_tac) >>
      simp[cSOMEP_EQN, EXISTS_PROD, PULL_EXISTS]) >>
  first_x_assum (qspecl_then [`hi - 1`, `lo`] mp_tac) >> simp[] >>
  simp[Num_EQ_num] >>
  `Num (hi - 1 - lo) = sz` by simp[Num_EQ_num] >> simp[] >>
  simp[GSYM integerTheory.INT_ADD] >>
  `∀x:int. hi - 1 - x = hi - (x + 1)` by simp[] >>
  `∀x:int. x + 1 + 1 = x + 2` by simp[] >> simp[])

val iSOMEP_def = Define`
  ((iSOMEP) P NONE ⇔ T) ∧
  ((iSOMEP) P (SOME v) ⇔ P v)
`;
val _ = export_rewrites ["iSOMEP_def"]
val _ = set_fixity "iSOMEP" Binder

val iSOMEP_OPTION_BIND_I = store_thm(
  "iSOMEP_OPTION_BIND_I",
  ``∀P Q f v. (iSOMEP) P v ∧ (∀z. P z ⇒ (iSOMEP) Q (f z)) ⇒
              (iSOMEP) Q (OPTION_BIND v f)``,
  rpt gen_tac >> Cases_on `v` >> simp[]);

val iSOMEP_OPTION_IGNORE_BIND = store_thm(
  "iSOMEP_OPTION_IGNORE_BIND",
  ``∀Q v1 v2.
        (iSOMEP) Q (OPTION_IGNORE_BIND v1 v2) ⇔
        ∀v0. v1 = SOME v0 ⇒ (iSOMEP) Q v2``,
  rpt gen_tac >> Cases_on `v1` >> simp[]);

val iSOMEP_assert_BIND = store_thm(
  "iSOMEP_assert_BIND[simp]",
  ``∀Q v b.
      (iSOMEP) Q (OPTION_IGNORE_BIND (assert b) v) ⇔ b ⇒ (iSOMEP) Q v``,
  Cases_on `b` >> simp[]);

val iSOMEP_EQN = store_thm(
  "iSOMEP_EQN",
  ``(iSOMEP) P v ⇔ ∀x. v = SOME x ⇒ P x``,
  Cases_on `v` >> simp[]);

val weak_for_rule = store_thm(
  "weak_for_rule",
  ``(∀lo hi.
       evalexpr m0 lo_e = Int lo ∧ evalexpr m0 hi_e = Int hi ⇒
       Inv lo (m0, ε) ∧
       (∀m g i. lo ≤ i ∧ i < hi ∧ Inv i (m,g) ⇒
                (iSOMEP (m',sg).  Inv (i + 1) (m', g ⊕ (HG sg <+ ε)))
                   (graphOf (Int i :: lab) m (ssubst v (Int i) s))) ∧
       (∀m g. Inv (int_max lo hi) (m, g) ⇒
              P (m, HD (addLabel lab
                           (domreadAction () m0 (D lo_e hi_e))) <+ g))) ⇒
      (iSOMEP) P (graphOf lab m0 (ForLoop v (D lo_e hi_e) s))``,
  simp[graphOf_def, dvalues_def, FOLDL_FOLDR_REVERSE, MAP_GENLIST] >>
  Cases_on `evalexpr m0 lo_e` >> simp[] >>
  Cases_on `evalexpr m0 hi_e` >> simp[] >>
  qcase_tac `evalexpr m0 lo_e = Int lo` >>
  qcase_tac `evalexpr m0 hi_e = Int hi` >>
  reverse (Cases_on `lo ≤ hi`) >> simp[]
  >- (rpt strip_tac >> `int_max lo hi = lo` by simp[] >>
      first_x_assum match_mp_tac >> simp[]) >>
  `int_max lo hi = hi` by simp[] >> simp[] >>
  simp[DECIDE ``PRE n - m = n - (m + 1)``, REVERSE_GENLIST] >>
  qabbrev_tac `sz = Num (hi - lo)` >>
  `∀m. m < sz ⇒ &(sz - (m + 1)) + lo = hi - &(m + 1)`
    by simp[int_arithTheory.INT_NUM_SUB, Abbr`sz`] >>
  pop_assum (fn th => simp[th, Cong GENLIST_CONG]) >> rpt strip_tac >>
  qunabbrev_tac `sz` >>
  match_mp_tac iSOMEP_OPTION_BIND_I >> qexists_tac `Inv hi` >>
  simp[FORALL_PROD] >>
  map_every (fn q => Q.UNDISCH_THEN q kall_tac) [
    `evalexpr m0 lo_e = Int lo`, `evalexpr m0 hi_e = Int hi`,
    `int_max lo hi = hi`
  ] >>
  qpat_assum `∀m g. Inv hi (m,g) ==> X` kall_tac >>
  Induct_on `Num (hi - lo)` >> simp[] >> rpt strip_tac
  >- fs[Num_EQ_num] >>
  qcase_tac `SUC sz = Num (hi - lo)` >>
  fs[Num_EQ_num, arithmeticTheory.ADD1, GSYM integerTheory.INT_ADD] >>
  simp[integerTheory.INT_ADD, GENLIST_APPEND] >>
  match_mp_tac iSOMEP_OPTION_BIND_I >>
  qexists_tac `Inv (hi - 1)` >> simp[FORALL_PROD] >> reverse conj_tac
  >- (qx_genl_tac [`m1`, `g1`] >>
      first_x_assum (qspecl_then [`m1`, `g1`, `hi - 1`] mp_tac) >>
      simp[iSOMEP_EQN, EXISTS_PROD, PULL_EXISTS, FORALL_PROD]) >>
  first_x_assum (qspecl_then [`hi - 1`, `lo`] mp_tac) >> simp[] >>
  simp[Num_EQ_num] >>
  `Num (hi - 1 - lo) = sz` by simp[Num_EQ_num] >> simp[] >>
  simp[GSYM integerTheory.INT_ADD] >>
  `∀x:int. hi - 1 - x = hi - (x + 1)` by simp[] >>
  `∀x:int. x + 1 + 1 = x + 2` by simp[] >> simp[])

open PseudoCPropsTheory
val iSOMEP_OPT_SEQUENCE = store_thm(
  "iSOMEP_OPT_SEQUENCE",
  ``(iSOMEP) P (OPT_SEQUENCE l) ⇔
    (∀e. MEM e l ⇒ ∃v. e = SOME v) ⇒ P (MAP THE l)``,
  simp[iSOMEP_EQN, OPT_SEQUENCE_EQ_SOME]);

(*
val weak_par_rule = store_thm(
  "weak_par_rule",
  ``(∀lo hi.
       evalexpr m0 lo_e = Int lo ∧ evalexpr m0 hi_e = Int hi ⇒
       Inv lo (m0, ε) ∧
       (∀m g i m' sg.
          lo ≤ i ∧ i < hi ∧ Inv i (m,g) ∧
          graphOf (Int i :: lab) m (ssubst v (Int i) s) = SOME(m',sg) ∧
          sg ≁ᵍ g ⇒
          Inv (i + 1) (m', g ⊕ (HG sg <+ ε))) ∧
       (∀m g. Inv (int_max lo hi) (m, g) ⇒
              P (m, HD (addLabel lab
                           (domreadAction () m0 (D lo_e hi_e))) <+ g))) ⇒
      (iSOMEP) P (graphOf lab m0 (ParLoop v (D lo_e hi_e) s))``,
  simp[graphOf_def, dvalues_def, FOLDL_FOLDR_REVERSE, MAP_GENLIST] >>
  Cases_on `evalexpr m0 lo_e` >> simp[] >>
  Cases_on `evalexpr m0 hi_e` >> simp[] >>
  qcase_tac `evalexpr m0 lo_e = Int lo` >>
  qcase_tac `evalexpr m0 hi_e = Int hi` >>
  reverse (Cases_on `lo ≤ hi`) >> simp[]
  >- (rpt strip_tac >> `int_max lo hi = lo` by simp[] >>
      simp[OPT_SEQUENCE_def]) >>
  `int_max lo hi = hi` by simp[] >> simp[] >>
  simp[MAP_GENLIST, combinTheory.o_ABS_R] >> rpt strip_tac >>
  match_mp_tac iSOMEP_OPTION_BIND_I >>
  simp[FORALL_PROD, iSOMEP_OPT_SEQUENCE, MEM_GENLIST, MAP_GENLIST,
       PULL_EXISTS, combinTheory.o_ABS_R] >>
  qexists_tac `
    λgl. (iSOMEP) P
         (do
           assert(∀i j. i < j ∧ j < LENGTH gl ⇒ EL i gl ≁ᵍ EL j gl);
           m <- pcg_eval (FOLDR (λg acc. HG g <+ acc) ε gl) (SOME m0);
           SOME (m, HD (addLabel lab (domreadAction () m0 (D lo_e hi_e))) <+
                    FOLDR (λg acc. HG g <+ acc) ε gl)
          od)` >>
  simp[] >>
  simp[SimpL ``(==>)``, SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  disch_then (qx_choosel_then [`GG`] assume_tac) >>
  simp[Cong GENLIST_CONG] >> strip_tac >>
  match_mp_tac iSOMEP_OPTION_BIND_I >> simp[] >>
  qexists_tac `
    λm. Inv hi (m,
                FOLDR (λg acc. HG g <+ acc) ε
                      (GENLIST (λn. SND (GG n)) (Num (hi - lo))))
  ` >> simp[] >>
  map_every (fn q => Q.UNDISCH_THEN q kall_tac) [
    `evalexpr m0 lo_e = Int lo`, `evalexpr m0 hi_e = Int hi`,
    `int_max lo hi = hi`
  ] >>
  qpat_assum `∀m g. Inv hi (m,g) ==> X` kall_tac >>
  `∃n. hi = lo + &n`
    by (`∃i. hi = lo + i ∧ 0 ≤ i` by simp[] >>
        qexists_tac `Num i` >> metis_tac[integerTheory.INT_OF_NUM]) >>
  pop_assum SUBST_ALL_TAC >> fs[] >>
  `∃n0. n0 ≤ n ∧ n0 = n` by simp[] >>
  pop_assum (SUBST1_TAC o SYM) >> Induct_on `n0`
*)
val _ = export_theory();
