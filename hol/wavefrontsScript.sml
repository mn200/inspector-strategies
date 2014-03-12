open HolKernel Parse boolLib bossLib;

open actionGraphTheory datadepsTheory
open sortingTheory

val _ = new_theory "wavefronts";

val wavesort_def = Define`
  wavesort G l = QSORT (wave G LEX (<)) l
`;

val _ = export_theory();
