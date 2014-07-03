open HolKernel Parse boolLib bossLib;

open PseudoCTheory

val _ = new_theory "fastwave";

val summationLoop_def = Define`
  summationLoop =
    [
        AssignVar "sum" Value(Real(0.0));
        ForLoop "k" (D (Value(Int 0)) (VarExp "workPerIter") )
            AssignVar "sum"
                (Opn plusval [
                    VarExp "sum";
                    Opn divval [
                        Value (Real 1.0);
                        Opn expval [
                            Opn multval [
                                Opn multval [
                                    VRead "k";
                                    ARead "data_org"
                                        (ISub "row" (VarExp "p"))
                                ];
                                ARead "data_org"
                                    (ISub "col" (VarExp "p"))
                            ]
                        ]
                    ]
                ])
    ]`;

val orgbody_def = Define`
  orgbody = summationLoop ++
    [
        (* data_org[ row[p] ] += 1.0 + sum; *)
        Assign ("data_org", (ISub "row" (VarExp "p")))
            [ ARead "data_org" (ISub "row" (VarExp "p"));
              VRead "sum
            ]
            (\p . plusval [HD p; Real 1.0; HD (TL p)])

        (* data_org[ col[p] ] += 1.0 + sum; *)
        Assign ("data_org", (ISub "col" (VarExp "p")))
            [ ARead "data_org" (ISub "col" (VarExp "p"));
              VRead "sum
            ]
            (\p . plusval [HD p; Real 1.0; HD (TL p)])
    ]`

val original_def = Define`
  original = ForLoop "p" (D (Value(Int 0)) (VarExp "nnz")) (Seq orgbody))
`;

val _ = export_theory();
