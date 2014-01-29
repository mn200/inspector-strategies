open HolKernel Parse boolLib bossLib;
open primitivesTheory
open lcsymtacs

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
