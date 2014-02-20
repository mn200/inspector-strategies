open HolKernel Parse boolLib bossLib;

val _ = new_theory "wavefronts";

(*

where j and i are iteration numbers

  wave(i) = max_set { wave(j) + 1 | j | (j,i) ∈ Deps}

relying on well-foundedness of Deps

then, sort wrt wave function (lexicographic sort of (wave(i), i)),
giving a permutation of [0..N), and thus a δ that respects the graph's
dependencies, and satisfies precondition of datadepsTheory.correctness

*)



val _ = export_theory();
