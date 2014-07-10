(* HOL specification of the original, inspector, and executor
 * for wavebench. *)
(* testing changes *)

open HolKernel Parse boolLib bossLib;

open PseudoCTheory PseudoCOpsTheory

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
                (\xs . case xs of [s;k;drow;dcol] =>
                                  s + ((Real 1.0) / (exp (k*drow*dcol)) )))
    ]`;

val orgbody_def = Define`
  orgbody = summationLoop ++
    [
        (* data_org[ row[p] ] += 1.0 + sum; *)
        Assign ("data_org",  ARead "row" (VRead "p"))
            [ DARead "data_org" (ARead "row" (VRead "p"));
              DVRead "sum"
            ]
            (\ xs . case xs of [d;s] => (Real 1.0) + d + s);

        (* data_org[ col[p] ] += 1.0 + sum; *)
        Assign ("data_org", (ARead "col" (VRead "p")))
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
        (*Malloc "lw_iter" (VRead "N") (Int (-1));
        Malloc "lr_iter" (VRead "N") (Int (-1));
        Malloc "wave" (VRead "nnz") (Int 0);*)
        Malloc "lw_iter" 99 (Int (-1));
        Malloc "lr_iter" 99 (Int (-1));
        Malloc "wave" 99 (Int 0);
        AssignVar "max_wave" [] (\xs . Int 0);

        ForLoop "p" (D (Value(Int 1)) (VRead "nnz") )
            (Seq [
                  Assign 
                      ("lr_iter",
                       (ARead "row" 
                              (Opn minusval [VRead "p"; Value(Int(1))] )))
                      [DVRead "p"]
                      (\xs . case xs of [p] => p - (Int 1) )
            ]);

        IfStmt  (Opn cmpGTEval [(ARead "lw_iter" (VRead "r")); 
                                (Value(Int(0)))] )
                (Assign
                     ("wave",VRead "p")
                     [DARead "wave" (VRead "p");
                      DARead "wave" (ARead "lw_iter" (VRead "r"))]
                     (\xs . case xs of [x;y] => maxval [x; y + (Int 1)])
                )
                (Seq [])


    ]
`


val _ = export_theory();
