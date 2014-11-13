open HolKernel Parse boolLib bossLib;

open pred_setTheory
open listTheory
open pairTheory
open PseudoCTheory
open PseudoCOpsTheory
open PseudoCPropsTheory
open hidagTheory
open PseudoCHDAGTheory

val _ = new_theory "forparConvert";

(* for compatibility with old PC syntax *)
val _ = temp_overload_on ("ARead", ``λs e. MAccess (ASub (VRead s) e)``)
val _ = temp_overload_on ("VarExpr", ``λs. MAccess (VRead s)``)

(*
Would like this equivalence between old code and executor:

    for (i ∈ d) { body } ==

    for (w ∈ 0 .. wavedepth g) {
      parfor (p ∈ 0 .. wsizes[w])
        body[ i := wave_doms[wave_offs[w] + p] ]

But will first aim for the simpler (less realistic):

    for (i ∈ d) { body } ==

    for (w ∈ 0 .. wavedepth g) {
      parfor (i ∈ d) {
        if (wave[i] == w) { body }
      }
    }

where the wave array maps iteration numbers to wave number.

*)
val simple_executor_equivalence = store_thm(
  "simple_executor_equivalence",
  ``graphOf lab0 m0 (ForLoop i d body) = SOME(m,g) ⇒
    ∃g'.
      graphOf lab0 m0
        (ForLoop
           w
           (D (Value (Int 0)) (Value (Int &(wavedepth g))))
           (ParLoop i d
              (IfStmt (ARead wave_a (VarExpr i) == VarExpr w)
                      body
                      Done))) = SOME(m,g') ∧
      strip_disconnected_reads g' = g``,
  NO_TAC);

val _ = export_theory();
