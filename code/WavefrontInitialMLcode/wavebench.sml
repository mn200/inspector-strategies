(* Wavebench original code, inspector, and executor implemented
 * with the low-level inspector/executor AST. 
 *)
use "PseudoC.sml";

(**** Original Computation ****)

(* incoming parameter values and small_test_5.5.mm sparse matrix *)
(*
val nnz = 13
val N = 5
val workPerIter = 4
val rowlist = [ 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4 ]
val collist = [ 0, 1, 2, 1, 2, 3, 2, 3, 4, 3, 4, 0, 4 ]

(* put data_org array of reals into environment *)
val initEnv = envupdate ( empty_env, "data_org", 
                          RealVecVal(empty_dv(Domain1D(0,N),1.0)) )
val initEnv = envupdate ( initEnv, "sum",
                          RealVecVal(empty_dv(Domain1D(0,1),0.0)) )

(* put row and col index arrays into environment *)
val initEnv = envupdate ( initEnv, "row", 
                          (IVecVal (list_to_ivector rowlist (Domain1D(0,N)))) )
val initEnv = envupdate ( initEnv, "col", 
                          (IVecVal (list_to_ivector collist (Domain1D(0,N)))) )
*)

(* Specification of the original computation *)

val summation = SeqStmt(
        [
          AssignVar("sum",Value(Real(0.0))),
          ForLoop("k",D1D(Value(Int(0)),VarExp("workPerIter")),
                  AssignVar(
                      "sum",
                      Plus(
                          VarExp("sum"),
                          Divide(
                              Value(Real(1.0)),
                              Exp(
                                  Mult(
                                      Mult(
                                          Convert(VarExp("k")),
                                          ARead("data_org",
                                                ARead("row",VarExp("p")))),
                                      ARead("data_org",
                                            ARead("col",VarExp("p")))))))))
        ])


val summation_test = print (genCstmt summation 0)


val orgbody = 
    SeqStmt(
        [
          summation,
          Assign("data_org",ARead("row",VarExp("p")),
                 Plus(
                     ARead("data_org",ARead("row",VarExp("p"))),
                     Plus(Value(Real(1.0)),VarExp("sum")))),
          Assign("data_org",ARead("col",VarExp("p")),
                 Plus(
                     ARead("data_org",ARead("col",VarExp("p"))),
                     Plus(Value(Real(1.0)),VarExp("sum"))))
        ]
    )

val original = ForLoop("p",D1D(Value(Int(0)),VarExp("nnz")),orgbody)


val original_test = print (genCstmt original 0)


(**** Wavefront Inspector and Executor in PseudoC****)
(* Using parameters nnz, N, row, col, and initEnv
 * from above original computation. 
 *)

(* Comments for the below code are in 
 * benchmarks/wavebench/wavebench-driver.cpp *)

val inspector = SeqStmt(
        [ Malloc("lw_iter", VarExp("N"), Int(~1)),
          Malloc("lr_iter", VarExp("N"), Int(~1)),
          Malloc("wave", VarExp("nnz"), Int(0)),
          AssignVar("max_wave",Value(Int(0))),
          ForLoop("p",D1D(Value(Int(1)),VarExp("nnz")),
                  SeqStmt([
                    Assign("lr_iter",
                           ARead("row",Minus(VarExp("p"),Value(Int(1)))),
                           Minus(VarExp("p"),Value(Int(1)))),
                    Assign("lr_iter",
                           ARead("col",Minus(VarExp("p"),Value(Int(1)))),
                           Minus(VarExp("p"),Value(Int(1)))),
                    Assign("lw_iter",
                           ARead("row",Minus(VarExp("p"),Value(Int(1)))),
                           Minus(VarExp("p"),Value(Int(1)))),
                    Assign("lw_iter",
                           ARead("col",Minus(VarExp("p"),Value(Int(1)))),
                           Minus(VarExp("p"),Value(Int(1)))),
                    AssignVar("r",ARead("row",VarExp("p"))),
                    AssignVar("c",ARead("col",VarExp("p"))),
                    IfStmt(CmpGTE(ARead("lw_iter",VarExp("r")),Value(Int(0))),
                           Assign("wave",VarExp("p"),
                                  Max(ARead("wave",VarExp("p")),
                                      Plus(ARead("wave",
                                                 ARead("lw_iter",VarExp("r"))),
                                           Value(Int(1))))),
                          SeqStmt([])),
                    IfStmt(CmpGTE(ARead("lr_iter",VarExp("r")),Value(Int(0))),
                           Assign("wave",VarExp("p"),
                                  Max(ARead("wave",VarExp("p")),
                                      Plus(ARead("wave",
                                                 ARead("lw_iter",VarExp("r"))),
                                           Value(Int(1))))),
                          SeqStmt([])),
                    IfStmt(CmpGTE(ARead("lw_iter",VarExp("c")),Value(Int(0))),
                           Assign("wave",VarExp("p"),
                                  Max(ARead("wave",VarExp("p")),
                                      Plus(ARead("wave",
                                                 ARead("lw_iter",VarExp("c"))),
                                           Value(Int(1))))),
                          SeqStmt([])),
                    IfStmt(CmpGTE(ARead("lr_iter",VarExp("c")),Value(Int(0))),
                           Assign("wave",VarExp("p"),
                                  Max(ARead("wave",VarExp("p")),
                                      Plus(ARead("wave",
                                                 ARead("lr_iter",VarExp("c"))),
                                           Value(Int(1))))),
                          SeqStmt([])),
                    AssignVar("max_wave",Max(VarExp("max_wave"),
                                             ARead("wave",VarExp("p"))))
                         ]) ),
          Malloc("wavestart",  Plus(VarExp("max_wave"),Value(Int(2))), Int(0)),
          ForLoop("p",D1D(Value(Int(0)),VarExp("nnz")),
                   Assign("wavestart",ARead("wave",VarExp("p")),
                          Plus(ARead("wavestart",ARead("wave",VarExp("p"))),
                               Value(Int(1))))),
          ForLoop("w",D1D(Value(Int(1)),Plus(VarExp("max_wave"),Value(Int(2)))),
                   Assign("wavestart",VarExp("w"),
                          Plus(ARead("wavestart",
                                     Minus(VarExp("w"),Value(Int(1)))),
                               ARead("wavestart",VarExp("w"))))),
          Malloc("wavefronts",  VarExp("nnz"), Int(0)),
          ForLoop("prev",D1D(Value(Int(1)),Plus(VarExp("nnz"),Value(Int(1)))),
                  SeqStmt([
                             AssignVar("p",Minus(VarExp("nnz"),VarExp("prev"))),
                             AssignVar("w",ARead("wave",VarExp("p"))),
                             Assign("wavestart",VarExp("w"),
                                    Minus(ARead("wavestart",VarExp("w")),
                                          Value(Int(1)))),
                             Assign("wavefronts",
                                    ARead("wavestart",VarExp("w")),
                                    VarExp("p"))
                         ]))

        ]
 )

val inspector_test = print (genCstmt inspector 0)


val executor =
    ForLoop("w",D1D(Value(Int(0)),VarExp("max_wave")),
            ParForLoop("k",D1D(ARead("wavestart",VarExp("w")),
                               ARead("wavestart",Plus(VarExp("w"),
                                                      Value(Int(1))))),
                       SeqStmt(
                           [
                             AssignVar("p",ARead("wavefronts",VarExp("k"))),
                             orgbody
                           ]
                       )))

val executor_test = print (genCstmt executor 0)
