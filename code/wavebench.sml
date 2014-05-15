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
          DAssign("sum",Value(Int(0)),[],(fn []=>Value(Real(0.0)))),
          ForLoop("k",D1D(Value(Int(0)),VarExp("workPerIter")),
                  DAssign("sum",Value(Int(0)),
                          [ARead("data_org",ARead("row",VarExp("p"))),
                           ARead("data_org",ARead("col",VarExp("p"))),
                           ARead("sum",Value(Int(0)))],
                          (fn di::dj::sum::[]=>
                              Plus(sum,
                                   Divide(Value(Real(1.0)),
                                          Exp(
                                              Mult(
                                                  Mult(
                                                      Convert(VarExp("k")),di),
                                                  dj))))) ) )
        ])


(*
                           [ARead("data_org",ARead("row",VarExp("p"))),
                            ARead("data_org",ARead("col",VarExp("p")))],
                           (fn xi::xj::[] =>
                                ForLoop("k",D1D(Value(Int(0)),
                                                VarExp("workPerIter")),
                                        DAssign("
                                    (fn Tuple1D(k) => fn sum =>
                                        sum + (1.0 / Math.exp(real(k)*xi*xj))) )
                                    0.0 ) )
*)
val summation_test = print (genCstmt summation 0)

(*
val original = ForLoop(["p"],Domain1D(0,nnz),
                       SeqStmt([summation,
                                AssignStmt("data_org",ISub("row",VarExp("p")),
                                       [Read("data_org",
                                             ISub("row",VarExp("p"))),
                                        Read("sum",Const(0))],
                                       (fn xi::sum::[] => xi + 1.0 + sum) ),
                                AssignStmt("data_org",ISub("col",VarExp("p")),
                                       [Read("data_org",
                                             ISub("col",VarExp("p"))),
                                         Read("sum",Const(0))],
                                       (fn xj::sum::[] => xj + 1.0 + sum) )]) )
*)

val original = DAssign("hello",Value(Int(0)),
                       [],(fn [] => Value(Int(7))))

val original_test = print (genCstmt original 0)


(**** Wavefront Inspector and Executor in PseudoC****)
(* Using parameters nnz, N, row, col, and initEnv
 * from above original computation. 
 *)

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
          Malloc("wavestart",  VarExp("max_wave"), Int(0))
        ]
 )

val inspector_test = print (genCstmt inspector 0)

(*
max_wave = MAX(max_wave,wave[p]);

AssignVar("max_wave", Opn( [VarExp("max_wave"), Convert( 
*)
