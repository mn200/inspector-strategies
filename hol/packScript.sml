open HolKernel Parse boolLib bossLib;

open primitivesTheory simpleLoopTheory

val _ = new_theory "pack";

val cpack_def = Define`
  cpack E =
     let visited = empty_v (rsizey E) F in
     let pack dinv dp visited y =
         if ¬ visited ' y then
           (update dinv dp y, dp + 1, update visited y T)
         else (dinv, dp, visited) in
     let (dinv, dp, visited) =
         RFOR X
              (λ(x,y) (dinv, dp, visited). pack dinv dp visited y)
              E
              (empty_v (rsizey E) 0, 0, visited) in
     let (dinv, dp, visited) =
         FOR (0, rsizey E)
             (λy (dinv,dp,visited). pack dinv dp visited y)
             (dinv, dp, visited)
     in
       dinv
`;







val _ = export_theory();
