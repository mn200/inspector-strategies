open HolKernel Parse boolLib bossLib;

open pred_setTheory
open listTheory
open pairTheory
open PseudoCTheory
open PseudoCPropsTheory
open actionGraphTheory

val _ = new_theory "forparConvert";

(*
for (v ∈ d) body  ==

for (w ∈ 0 .. gdepth g) {
  parfor (p ∈ 0 .. wsizes[w])
    body[ v := wave_doms[wave_offs[w] + p] ]
*)
(*
val simple_executor_equivalence = store_thm(
  "simple_executor_equivalence",
  ``graphOf i0 m0 (ForLoop v d body) = SOME(i,m,g) ⇒
    ∃i'.
      graphOf i0 m0
        (ForLoop
           w
           (D (Value 0) (gdepth g))
           (ParLoop
              p
              (D (Value 0) (ISub wsizes (VarExp w)))
              (ssubst v (ISub wave_doms
                              (Opn plusval [ISub wave_offs (VarExpr w);
                                            VarExpr p]))))) =
      SOME(i',m,g)``,
  NO_TAC);
*)



val _ = export_theory();
