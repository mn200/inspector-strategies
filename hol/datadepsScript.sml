open HolKernel Parse boolLib bossLib;
open primitivesTheory forLoopTheory pred_setTheory
open lcsymtacs

fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl

val _ = new_theory "datadeps";

val eval_def = Define`
  eval Wf Rs vf i A =
    update A (Wf i) (vf i (MAP (λf. vsub A (f i)) Rs))
`;

val example_t =
  ``FOR (0,N)
      (eval (vsub (f : num mvector))
            [(λi. i + 1); vsub (h : num mvector)]
            (λi rds. EL 0 rds + EL 1 rds + 1))``;

val computation =
    EVAL ``let N = 5 in
           let f = ((λi. EL i [4;3;2;1;0]), 5) in
           let h = ((λi. EL i [0;1;1;2;3]), 5) in
             ^example_t ((λi. EL i [0;0;0;0;0;0]), 6)``


(* C original:
int N = 5;
int A[6] = {0};
int f[5] = {4,3,2,1,0};
int h[5] = {0,1,1,2,3};

for (int i= 0; i < N; i++)
  A[f[i]] = A[i+1] + A [h[i]];


*)

val _ = overload_on("@@", ``λl x. MAP (combin$C I x) l``)
val _ = set_fixity "@@" (Infixl 2000)

val ddepR_def = Define`
  ddepR wf rfs i0 i ⇔
    i0 < i ∧ (wf i0 = wf i ∨
              MEM (wf i0) (rfs @@ i) ∨
              MEM (wf i) (rfs @@ i0))
`;

val ddepR_irreflexive = store_thm(
  "ddepR_irreflexive",
  ``∀i. ¬ddepR wf rfs i i``,
  rw[ddepR_def]);
val _ = export_rewrites ["ddepR_irreflexive"]

val ddepR_TC_LT = store_thm(
  "ddepR_TC_LT",
  ``∀i j. (ddepR wf rfs)⁺ i j ⇒ i < j``,
  ho_match_mp_tac relationTheory.TC_INDUCT >>
  rw[ddepR_def] >> decide_tac);

val ddepR_acyclic = store_thm(
  "ddepR_acyclic",
  ``∀i. ¬(ddepR wf rfs)⁺ i i``,
  rpt strip_tac >> imp_res_tac ddepR_TC_LT >> fs[]);
val _ = export_rewrites ["ddepR_acyclic"]

val vsz_eval = store_thm(
  "vsz_eval",
  ``vsz (eval wf rfs body i A) = vsz A``,
  simp[eval_def]);
val _ = export_rewrites ["vsz_eval"]

val vsz_eval_FOR = store_thm(
  "vsz_eval_FOR",
  ``vsz (FOR (lo,hi) (eval wf rfs body) A) = vsz A``,
  DEEP_INTRO_TAC FOR_RULE >> qexists_tac `λi A'. vsz A' = vsz A` >>
  simp[]);
val _ = export_rewrites ["vsz_eval_FOR"]

val vsub_eval_out_range_FOR = store_thm(
  "vsub_eval_out_range_FOR",
  ``(∀j. lo ≤ j ∧ j < hi ⇒ wf j ≠ i) ⇒ FOR (lo,hi) (eval wf rfs body) A ' i = A ' i``,
  strip_tac >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λj a. a ' i = A ' i` >> simp[eval_def] >>
  simp[update_sub]);

(* now convinced that this approach, based on what was done for
"simple" loops, can't work because it's hard to imagine using it
anything about the contents of the array part-way through the loop. In
the simple case, a given index had either been written or had not.
Here, depending on the wf array/function, an array cell may be written
multiple times.

val correct0 = prove(
  ``BIJ δ (count N) (count N) ∧ Abbrev (γ = LINV δ (count N)) ∧
    (∀j. j < N ⇒ wf j < N) ∧
    (final = FOR (0,N) (eval wf rfs body) A1) ∧
    (∀i0 i. ddepR wf rfs i0 i ==> δ i0 < δ i) ⇒
    ∀m n A2.
      (vsz A1 = vsz A2) ∧ N ≤ vsz A1 ∧
      (m = N - n) ∧ n ≤ N ∧
      (∀i. A2 ' i = if i ∈ IMAGE δ (count n) then vsub final i
                    else vsub A1 i)
     ⇒
      (FOR (n, N) (eval (wf o γ) (MAP (λf. f o γ) rfs) body) A2 = final)``,
  strip_tac >> Induct >| [
    rpt strip_tac >> `N = n` by decide_tac >>
    qpat_assum `0 = N - n` kall_tac >>
    srw_tac[ARITH_ss][] >>
    srw_tac[ARITH_ss][vector_EQ] >>
    Cases_on `i < N`
    >- (`∃j. j < N ∧ (i = δ j)`
          by metis_tac[BIJ_DEF, IN_COUNT, SURJ_DEF] >>
        rw[] >> metis_tac[]) >>
    metis_tac[vsub_eval_out_range_FOR],

    rpt strip_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    srw_tac[ARITH_ss][] >> fs[AND_IMP_INTRO] >>
    first_x_assum match_mp_tac >> asimp[] >>
    `n < N` by decide_tac >>
    qx_gen_tac `i` >>
    `∀i. i < N ⇒ γ i < N`
      by (simp[Abbr`γ`] >> imp_res_tac BIJ_LINV_BIJ >>
          metis_tac[BIJ_DEF, SURJ_DEF, IN_COUNT]) >>
    reverse (Cases_on `i < N`)
    >- (`FOR (0,N) (eval wf rfs body) A1 ' i = A1 ' i`
          by metis_tac[vsub_eval_out_range_FOR] >>
        simp[] >>
        `A2 ' i = A1 ' i` by simp[] >>
        `i ≠ wf (γ n)` suffices_by
          simp[eval_def, update_sub] >>
        metis_tac[]) >>
    Cases_on `i = wf (γ n)`


    simp_tac (srw_ss()) [eval_def]

Cases_on `i = n` >| [
      pop_assum SUBST_ALL_TAC >>
      `n < N` by decide_tac >>
      `δ n < N` by metis_tac[BIJ_DEF, IN_COUNT, SURJ_DEF] >>
      simp_tac (srw_ss())[eval_def]
*)


(*
val correctness = store_thm(
  "correctness",
  ``(∀i0 i. ddepR wf rfs i0 i ==> δ i0 < δ i) ∧
    BIJ δ (count N) (count N) ∧
    γ = LINV δ (count N)
  ==>
    FOR (0,N) (eval wf rfs body) =
    FOR (0,N) (eval (wf o γ)
                    (MAP (λf. f o γ) rds)
                    body)``



*)
val _ = export_theory();
