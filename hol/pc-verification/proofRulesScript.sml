open HolKernel Parse boolLib bossLib;

open optionTheory pairTheory listTheory rich_listTheory
open indexedListsTheory PseudoCTheory PseudoCHDAGTheory

open lcsymtacs monadsyntax

val _ = new_theory "proofRules";

val _ = set_trace "Goalstack.print_goal_at_top" 0

val SOMEP_def = Define`
  ((SOMEP) P NONE ⇔ F) ∧
  ((SOMEP) P (SOME x) ⇔ P x)
`
val _ = export_rewrites ["SOMEP_def"]
val _ = set_fixity "SOMEP" Binder
val _ = augment_srw_ss [intSimps.OMEGA_ss]

val SOMEP_OPTION_BIND_I = store_thm(
  "SOMEP_OPTION_BIND_I",
  ``∀P R f v. $SOMEP R v ∧ (∀z. R z ⇒ $SOMEP P (f z)) ⇒
              $SOMEP P (OPTION_BIND v f)``,
  rpt gen_tac >> Cases_on `v` >> simp[]);

val SOMEP_EQN = store_thm(
  "SOMEP_EQN",
  ``$SOMEP P v ⇔ ∃x. v = SOME x ∧ P x``,
  Cases_on `v` >> simp[]);

val Num_EQ_num = store_thm(
  "Num_EQ_num",
  ``0 ≤ i ⇒ (Num i = n ⇔ i = &n) ∧ (n = Num i ⇔ i = &n)``,
  strip_tac >> simp[integerTheory.Num] >> SELECT_ELIM_TAC >> simp[] >>
  metis_tac [integerTheory.NUM_POSINT_EXISTS]);

val for_rule = store_thm(
  "for_rule",
  ``evalexpr m0 lo_e = Int lo ∧ evalexpr m0 hi_e = Int hi ∧
    Inv lo (m0, ε) ∧
    (∀m g i. lo ≤ i ∧ i < hi ∧ Inv i (m,g) ⇒
             (SOMEP (m',sg).  Inv (i + 1) (m', g ⊕ (HG sg <+ ε)))
               (graphOf (Int i :: lab) m (ssubst v (Int i) s))) ∧
    (∀m g. Inv (int_max lo hi) (m, g) ⇒
           P (m, HD (addLabel lab (domreadAction () m0 (D lo_e hi_e))) <+ g)) ⇒
      (SOMEP) P (graphOf lab m0 (ForLoop v (D lo_e hi_e) s))``,
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
  match_mp_tac SOMEP_OPTION_BIND_I >> qexists_tac `Inv hi` >>
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
  match_mp_tac SOMEP_OPTION_BIND_I >>
  qexists_tac `Inv (hi - 1)` >> simp[FORALL_PROD] >> reverse conj_tac
  >- (qx_genl_tac [`m1`, `g1`] >>
      first_x_assum (qspecl_then [`m1`, `g1`, `hi - 1`] mp_tac) >>
      simp[SOMEP_EQN, EXISTS_PROD, PULL_EXISTS]) >>
  first_x_assum (qspecl_then [`hi - 1`, `lo`] mp_tac) >> simp[] >>
  simp[Num_EQ_num] >>
  `Num (hi - 1 - lo) = sz` by simp[Num_EQ_num] >> simp[] >>
  simp[GSYM integerTheory.INT_ADD] >>
  `∀x:int. hi - 1 - x = hi - (x + 1)` by simp[] >>
  `∀x:int. x + 1 + 1 = x + 2` by simp[] >> simp[])

val _ = export_theory();
