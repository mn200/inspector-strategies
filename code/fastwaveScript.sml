(* HOL specification of the original, inspector, and executor
 * for wavebench. *)
(* testing changes *)

open HolKernel Parse boolLib bossLib;

open PseudoCTheory PseudoCOpsTheory

val _ = new_theory "fastwave";

val _ = overload_on ("DVRead", ``λs. DMA (VRead s)``)
val _ = overload_on ("ARead", ``λs e. MAccess (ASub (VRead s) e)``)
val _ = overload_on ("DARead", ``λanm e. DMA (ASub (VRead anm) e)``)
val _ = overload_on ("VRead", ``λs. MAccess (PseudoC$VRead s)``)
val _ = overload_on ("AssignVar", ``λs. Assign (VRead s)``)
val _ = overload_on ("LVSub", ``λnm e. ASub (VRead nm) e``)

val summationLoop_def = Define`
  summationLoop =
    [
        AssignVar "sum" [] (\xs . Real 0);
        ForLoop "k" (D (Value(Int 0)) (VRead "workPerIter"))
            (AssignVar "sum" [DVRead "sum";
                              DVRead "k";
                              DARead "data_org" (ARead "row" (VRead "p"));
                              DARead "data_org" (ARead "col" (VRead "p"))]
                (\xs . case xs of [s;k;drow;dcol] =>
                                  s + ((Real 1.0) / (exp (k*drow*dcol)) )))
    ]`;

val orgbody_def = Define`
  orgbody = summationLoop ++
    [
        (* data_org[ row[p] ] += 1.0 + sum; *)
        Assign (LVSub "data_org"  (ARead "row" (VRead "p")))
            [ DARead "data_org" (ARead "row" (VRead "p"));
              DVRead "sum"
            ]
            (\ xs . case xs of [d;s] => (Real 1.0) + d + s);

        (* data_org[ col[p] ] += 1.0 + sum; *)
        Assign (LVSub "data_org" (ARead "col" (VRead "p")))
            [ DARead "data_org" (ARead "col" (VRead "p"));
              DVRead "sum"
            ]
            (\xs . case xs of [d;s] =>  (Real 1.0) + d + s)
    ]`

val original_def = Define`
  original = ForLoop "p" (D (Value(Int 0)) (VRead "nnz")) (Seq orgbody)
`;

val findWavesFast_def = Define`
  findWavesFast =
    Seq [
        Malloc "lw_iter" (VRead "N") (Int (-1));
        Malloc "lr_iter" (VRead "N") (Int (-1));
        Malloc "wave" (VRead "nnz") (Int 0);
        AssignVar "max_wave" [] (\xs . Int 0);

        ForLoop "p" (D (Value(Int 1)) (VRead "nnz") )
            (Seq [

                  Assign
                      (LVSub "lr_iter"
                       (ARead "row"
                              (Opn minusval [VRead "p"; Value(Int(1))] )))
                      [DVRead "p"]
                      (\xs . case xs of [p] => p - (Int 1) );
                  Assign
                      (LVSub "lr_iter"
                       (ARead "col"
                              (Opn minusval [VRead "p"; Value(Int(1))] )))
                      [DVRead "p"]
                      (\xs . case xs of [p] => p - (Int 1) );
                  Assign
                      (LVSub "lw_iter"
                       (ARead "row"
                              (Opn minusval [VRead "p"; Value(Int(1))] )))
                      [DVRead "p"]
                      (\xs . case xs of [p] => p - (Int 1) );
                  Assign
                      (LVSub "lw_iter"
                       (ARead "col"
                              (Opn minusval [VRead "p"; Value(Int(1))] )))
                      [DVRead "p"]
                      (\xs . case xs of [p] => p - (Int 1) );

                  AssignVar "r" [DARead "row" (VRead "p")] (\xs . case xs of [r] => r);
                  AssignVar "c" [DARead "col" (VRead "p")] (\xs . case xs of [c] => c);

                  IfStmt  (Opn cmpGTEval [(ARead "lw_iter" (VRead "r"));
                                (Value(Int(0)))] )
                       (Assign
                         (LVSub "wave" (VRead "p"))
                         [DARead "wave" (VRead "p");
                          DARead "wave" (ARead "lw_iter" (VRead "r"))]
                         (\xs . case xs of [x;y] => maxval [x; y + (Int 1)])
                        )
                        (Seq []);
                  IfStmt  (Opn cmpGTEval [(ARead "lr_iter" (VRead "r"));
                                (Value(Int(0)))] )
                        (Assign
                          (LVSub "wave" (VRead "p"))
                          [DARead "wave" (VRead "p");
                           DARead "wave" (ARead "lr_iter" (VRead "r"))]
                          (\xs . case xs of [x;y] => maxval [x; y + (Int 1)])
                        )
                        (Seq []);
                  IfStmt  (Opn cmpGTEval [(ARead "lw_iter" (VRead "c"));
                                (Value(Int(0)))] )
                       (Assign
                         (LVSub "wave" (VRead "p"))
                         [DARead "wave" (VRead "p");
                          DARead "wave" (ARead "lw_iter" (VRead "c"))]
                         (\xs . case xs of [x;y] => maxval [x; y + (Int 1)])
                        )
                        (Seq []);
                  IfStmt  (Opn cmpGTEval [(ARead "lr_iter" (VRead "c"));
                                (Value(Int(0)))] )
                        (Assign
                          (LVSub "wave" (VRead "p"))
                          [DARead "wave" (VRead "p");
                           DARead "wave" (ARead "lr_iter" (VRead "c"))]
                          (\xs . case xs of [x;y] => maxval [x; y + (Int 1)])
                        )
                        (Seq []);
                  AssignVar "max_wave"
                    [DVRead "max_wave"; DARead "wave" (VRead "p")]
                    (\xs . case xs of [x;y] => maxval [x; y])

            ]);

            Malloc "wavestart" (Opn plusval [VRead "max_wave"; Value (Int 2)] )
                (Int(0));

            ForLoop "p" (D (Value(Int 0)) (VRead "nnz") )
                (Assign (LVSub "wavestart" (ARead "wave" (VRead "p")))
                    [DARead "wavestart" (ARead "wave" (VRead "p"))]
                    (\xs . case xs of [w] => w - Int 1));

            ForLoop "w" (D (Value(Int 1))
                           (Opn plusval [(VRead "max_wave"); (Value(Int 1)) ]))
                (Assign (LVSub "wavestart" (VRead "w"))
                    [DARead "wavestart" (Opn minusval [(VRead "w"); (Value(Int 1))]);
                     DARead "wavestart" (VRead "w")]
                    (\xs . case xs of [x;y] => x + y));

            Malloc "wavefronts" (VRead "nnz") (Int 0);
            ForLoop "prev" (D (Value(Int 1)) (Opn plusval [(VRead "nnz");
                                                           (Value(Int 1))] ))
                (Seq [
                    AssignVar "p" [DVRead "nnz"; DVRead "prev"]
                      (\xs . case xs of [n;p] => n - p);
                    AssignVar "w" [DARead "wave" (VRead "p")]
                      (\xs . case xs of [w] => w);
                    Assign (LVSub "wavestart" (VRead "w"))
                        [DARead "wavestart" (VRead "w")]
                        (\xs . case xs of [ws] => ws - Int 1);
                    Assign (LVSub "wavefronts" (ARead "wavestart" (VRead "w")))
                        [DVRead "p"]
                        (\xs . case xs of [p] => p)
                ])
    ]
`

val executor_def = Define`
  executor =
    Seq [
      ForLoop "w" (D (Value(Int 0)) (VRead "max_wave"))
        (ParLoop "k" (D (ARead "wavestart" (VRead "w"))
                        (ARead "wavestart" (Opn plusval [VRead "w"; Value(Int 1)])))
            (Seq
                (AssignVar "p" [DARead "wavefronts" (VRead "k")]
                  (\xs . case xs of [w] => w)
                  ::
                orgbody)
            )
         )

    ]
`

val _ = export_theory();
