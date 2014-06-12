-- C code generator for wavebench-driver.
--
-- find_waves_fast_gen, rauchwerger95, and zhuang09 are respresented
-- in PIES directly in ASTs and then explicit relation construction
-- removal happens followed by lowering to PseudoC and the C code generation.
--
-- Status: Generates stubs for all three inspectors.

module Main where

import PseudoC

main::IO()
main = do 
        putStrLn (genWaveInspector "find_waves_fast_gen"  findWavesFast)
        putStrLn (genWaveInspector "rauchwerger95"  stub)
        putStrLn (genWaveInspector "zhuang09"  stub)
        
tab :: String
tab = "    "

-- stub inspector that just mallocs and sets minimal vars for C compile
stub :: PseudoC.Stmt
stub = SeqStmt
        [AssignVar "max_wave" (Value (IntVal(0))),
         Malloc "wavestart" 
                (Plus (VarExpr("max_wave")) (Value (IntVal(2))))
                (IntVal 0),
         Malloc "wavefronts" (VarExpr("nnz")) (IntVal 0)
        ]


-- PseudoC representation of find_waves_fast_gen inspector
findWavesFast :: PseudoC.Stmt
findWavesFast = SeqStmt [
    Malloc "lw_iter" (VarExpr "N")  (IntVal (-1)),
    Malloc "lr_iter" (VarExpr "N")  (IntVal (-1)),
    Malloc "wave"    (VarExpr "nnz") (IntVal 0),
    AssignVar "max_wave" (Value (IntVal 0)),
    ForLoop "p" (D1D (Value(IntVal 1)) (VarExpr "nnz"))
        (SeqStmt [
            Assign "lr_iter"
                (ARead "row" (Minus (VarExpr "p") (Value(IntVal 1))))
                (Minus (VarExpr "p") (Value(IntVal 1))),
            Assign "lr_iter"
                (ARead "col" (Minus (VarExpr "p") (Value(IntVal 1))))
                (Minus (VarExpr "p") (Value(IntVal 1))),
            Assign "lw_iter"
                (ARead "row" (Minus (VarExpr "p") (Value(IntVal 1))))
                (Minus (VarExpr "p") (Value(IntVal 1))),
            Assign "lw_iter"
                (ARead "col" (Minus (VarExpr "p") (Value(IntVal 1))))
                (Minus (VarExpr "p") (Value(IntVal 1))),
            AssignVar "r" (ARead "row" (VarExpr "p")),
            AssignVar "c" (ARead "col" (VarExpr "p"))
        ])
    ]
{-|        
            IfStmt (CmpGTE (ARead("lw_iter",VarExp("r")) Value(Int(0)),
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
-}



-- Given the inspector function name and AST generate the C inspector function.
-- Generates the stub needed by wavebench-driver.cpp.
-- FIXME: might want to move into PseudoC since have C code.
genWaveInspector :: String -> PseudoC.Stmt -> String
genWaveInspector inspecName inspecAST =
        "void " ++ inspecName 
        ++ "(COO_mat *mat, int nnz, int * row, int *col,\n"
        ++ tab ++ tab ++ "int *max_wave_ptr, int **wavestart_ptr,\n"
        ++ tab ++ tab ++ "int **wavefronts_ptr) {\n"
        ++ (genCstmt inspecAST 1)
        ++ tab ++ "\n"
        ++ tab ++ "// epilogue to capture outputs\n"
        ++ tab ++ "(*max_wave_ptr) = max_wave;\n"
        ++ tab ++ "(*wavestart_ptr) = wavestart;\n"
        ++ tab ++ "(*wavefronts_ptr) = wavefronts;\n"
        ++ "}\n"
