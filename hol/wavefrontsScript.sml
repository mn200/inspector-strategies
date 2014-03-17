open HolKernel Parse boolLib bossLib;

open actionGraphTheory datadepsTheory
open sortingTheory relationTheory

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

val wavesort_def = Define`
  wavesort G l =
    QSORT (inv_image (inv_image (<=) (wave G) LEX (<=)) (λe. (e,e))) l
`;

val _ = export_theory();
