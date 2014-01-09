open HolKernel Parse boolLib bossLib;

val _ = new_theory "datadeps";

val eval_def = Define`
  eval A body Wf Rs i =
    update A (Wf i) (body (MAP (λf. f i) Rs))
`;

(* C original:
for (int i= 0; i < N; i++)
  A[f[i]] = A[i+1] + A [h[i]];

for (int j=lo; j < M; j++)
  A[f[

*)

val eg1_def = Define`
  FOR (0,100)
      (λi A.
        eval A (λris. A ' (EL 0 ris) + A ' (EL 1 ris))
             (λi. f ' i)
             [(λi. g ' i); (λi. h ' i)]
             i)
`;


FOR (lo,hi) (λi A. eval f wi ris i)

val ddepR = Define`
  ddepR wf rfs i0 i ⇔
    i0 < i ∧ (wf i0 = wf i ∨
              MEM (wf i0) (rfs i) ∨
              MEM (wf i) (rfs i0))
`;


domain1 = domain2 ∧ wi' = wi o dinv ∧ ris' = ris' o dinv ∧
BIJ dinv (count N) (count N)


(ddepR wf rfs i0 i ==> δ i0 < δ i (in domain2))
∧
 BIJ δ domain1 domain2

==>

FOR i ∈ domain1 { update A wf rfs i } =
FOR j ∈ domain2 { update A (wf o δ⁻¹) (rfs o δ⁻¹) j }




val _ = export_theory();
