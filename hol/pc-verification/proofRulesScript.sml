open HolKernel Parse boolLib bossLib;

open PseudoCHDAGTheory

open lcsymtacs

val _ = new_theory "proofRules";

val SOMEP_def = Define`
  ((SOMEP) P NONE ⇔ F) ∧
  ((SOMEP) P (SOME x) ⇔ P x)
`
val _ = export_rewrites ["SOMEP_def"]
val _ = set_fixity "SOMEP" Binder

val for_rule = store_thm(
  "for_rule",
  ``evalexpr m0 lo_e = Int lo ∧ evalexpr m0 hi_e = Int hi ∧
    Inv lo (m0, ε) ∧
    (∀m g i. lo ≤ i ∧ i < hi ∧ Inv i (m,g) ⇒
             (SOMEP (m',sg).  Inv (i + 1) (m', g ⊕ sg))
               (graphOf (Int i :: lab) m (ssubst v (Int i) s))) ∧
    (∀m g. Inv hi (m, g) ⇒ P (m, g)) ⇒
      (SOMEP) P (graphOf lab m0 (ForLoop v (D lo_e hi_e) s))``,
  ALL_TAC);

val _ = export_theory();
