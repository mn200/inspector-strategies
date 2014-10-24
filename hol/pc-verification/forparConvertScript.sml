open HolKernel Parse boolLib bossLib;

open pred_setTheory
open listTheory
open pairTheory
open PseudoCTheory
open PseudoCPropsTheory
open hidagTheory
open PseudoCHDAGTheory

val _ = new_theory "forparConvert";

(*
This equivalence between old code and executor:

    for (i ∈ d) { body } ==

    for (w ∈ 0 .. wavedepth g) {
      parfor (p ∈ 0 .. wsizes[w])
        body[ i := wave_doms[wave_offs[w] + p] ]

will hold when:

  1.


*)
val simple_executor_equivalence = store_thm(
  "simple_executor_equivalence",
  ``graphOf i0 m0 (ForLoop v d body) = SOME(m,g) ⇒
    ∃g'.
    graphOf i0 m0
        (ForLoop
           w
           (D (Value (Int 0)) (Value (Int &(wavedepth g))))
           (ParLoop
              p
              (D (Value 0) (ARead wsizes (VarExp w)))
              (Local v (ARead wavedoms
                              (Opn plusval [ARead wave_offs (VarExpr w);
                                            VarExpr p]))))) =
      SOME(m,g') ∧
      strip_disconnected_reads g' = g``,
  NO_TAC);

val _ = export_theory();
