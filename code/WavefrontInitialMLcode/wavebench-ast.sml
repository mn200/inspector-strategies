(* Wavebench original code, inspector, and executor implemented
 * with the low-level inspector/executor AST. 
 *)
use "primitives.sig";
use "primitives.sml";

use "ast.sml";

open primitives

(**** Original Computation ****)

(* incoming parameter values and small_test_5.5.mm sparse matrix *)
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

(* Specification of the original computation *)
val summation = AssignStmt("sum",Const(0),
                           [Read("data_org",ISub("row",VarExp("p"))),
                            Read("data_org",ISub("col",VarExp("p")))],
                           (fn xi::xj::[] =>
                                FOR (Domain1D(0,workPerIter))
                                    (fn Tuple1D(k) => fn sum =>
(print ("sum = " ^ (Real.toString(sum))^"\n");
                                        sum + (1.0 / Math.exp(real(k)*xi*xj))) )
                                    0.0 ) )

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

val original_test = dvector_to_list( getrealvec( 
                                         envlookup (
                                             (evalstmt original initEnv),
                                             "data_org")) )


(**** Wavefront Inspector and Executor in PseudoC****)
(* Using parameters nnz, N, row, col, and initEnv
 * from above original computation. 
 *)

val inspector = SeqStmt(
        [ Malloc("lw_iter", Domain1D(0,N), Domain1D(~1,nnz), Tuple1D(~1)),
          Malloc("lr_iter", Domain1D(0,N), Domain1D(~1,nnz), Tuple1D(~1)),
          Malloc("wave", Domain1D(0,nnz), Domain1D(0,nnz), Tuple1D(0)),
          Malloc("count", Domain1D(0,nnz), Domain1D(0,nnz), Tuple1D(0))
        ]
 )

val inspector_test = ivector_to_list( getivec( 
                                          envlookup 
                                              ( (evalstmt inspector initEnv),
                                              "lr_iter" )) )

(*
max_wave = MAX(max_wave,wave[p]);

AssignVar("max_wave", Opn( [VarExp("max_wave"), Convert( 
*)
