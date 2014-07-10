(* HOL specification of the original, inspector, and executor
 * for wavebench. *)

open HolKernel Parse boolLib bossLib;

open PseudoCTheory

val _ = new_theory "fastwave";

val summationLoop_def = Define`
  summationLoop =
    [
        AssignVar "sum" [] (\xs . Real 0);
        ForLoop "k" (D (Value(Int 0)) (VRead "workPerIter") )
            (AssignVar "sum" [DVRead "sum";
                              DVRead "k";
                              DARead "data_org" (ARead "row" (VRead "p"));
                              DARead "data_org" (ARead "col" (VRead "p"))]
                (\xs . plusval [
                    HD xs;
                    divval [
                        Real 1.0;
                        expval [
                            multval [
                                multval [
                                    HD (TL xs);
                                    HD (TL (TL xs))
                                ];
                                HD (TL (TL (TL xs)))
                            ]
                        ]
                    ]
                ]))
    ]`;

val orgbody_def = Define`
  orgbody = summationLoop ++
    [
        (* data_org[ row[p] ] += 1.0 + sum; *)
        Assign ("data_org",  ARead "row" (VRead "p"))
            [ DARead "data_org" (ARead "row" (VRead "p"));
              DVRead "sum"
            ]
            (\xs . plusval [HD xs; plusval [Real 1.0; HD (TL xs)]]);

        (* data_org[ col[p] ] += 1.0 + sum; *)
        Assign ("data_org", (ARead "col" (VRead "p")))
            [ DARead "data_org" (ARead "col" (VRead "p"));
              DVRead "sum"
            ]
            (\xs . plusval [HD xs; Real 1.0; HD (TL xs)])
    ]`

val original_def = Define`
  original = ForLoop "p" (D (Value(Int 0)) (VRead "nnz")) (Seq orgbody)
`;

val _ = export_theory();
