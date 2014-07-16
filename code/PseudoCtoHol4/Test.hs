-- hol code generator for test routine of PseudoC instructions.
--
-- find_waves_fast_gen, rauchwerger95, and zhuang09 are respresented
-- in PIES directly in ASTs and then explicit relation construction
-- removal happens followed by lowering to PseudoC and the hol code generation.
--
-- Status: Generates stubs for all three inspectors.

module Main where

import PseudoC

main::IO()
main = do 
 --       putStrLn (genWaveInspector "find_waves_fast_gen"  findWavesFast)
 --       putStrLn (genWaveInspector "rauchwerger95"  stub)
        putStrLn (genWaveInspector "zhuang09"  stub)
        
tab :: String
tab = "    "

-- stub inspector that just mallocs and sets minimal vars for C compile
stub :: PseudoC.Stmt
stub = SeqStmt
        [
         AssignVar "testInt" (Value (IntVal 1)),
         AssignVar "testBool" (Value (BoolVal True)),
         AssignVar "testBool2" (Value (BoolVal False)),
         AssignVar "testDouble" (Value (DoubleVal 0.0)),
         AssignVar "y" (VRead "testInt")
        ]

{-
-- PseudoC representation of find_waves_fast_gen inspector
--findWavesFast :: PseudoC.Stmt
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
                AssignVar "c" (ARead "col" (VarExpr "p")),
                IfStmt  (CmpGTE (ARead "lw_iter" (VarExpr "r")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VarExpr "p")
                                (Max (ARead "wave" (VarExpr "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lw_iter" (VarExpr "r")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                IfStmt  (CmpGTE (ARead "lr_iter" (VarExpr "r")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VarExpr "p")
                                (Max (ARead "wave" (VarExpr "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lr_iter" (VarExpr "r")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                IfStmt  (CmpGTE (ARead "lw_iter" (VarExpr "c")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VarExpr "p")
                                (Max (ARead "wave" (VarExpr "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lw_iter" (VarExpr "c")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                IfStmt  (CmpGTE (ARead "lr_iter" (VarExpr "c")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VarExpr "p")
                                (Max (ARead "wave" (VarExpr "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lr_iter" (VarExpr "c")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                AssignVar "max_wave" (Max (VarExpr "max_wave")
                                          (ARead "wave" (VarExpr "p")))
            ]),
            Malloc "wavestart" (Plus (VarExpr "max_wave") (Value(IntVal 2)))
                                (IntVal 0),
            ForLoop "p" (D1D (Value(IntVal 0)) (VarExpr "nnz"))
                (Assign "wavestart" (ARead "wave" (VarExpr "p"))
                    (Plus (ARead "wavestart" (ARead "wave" (VarExpr "p")))
                          (Value(IntVal 1)))),
            ForLoop "w" (D1D (Value(IntVal 1)) (Plus (VarExpr "max_wave")
                                                     (Value(IntVal 1))))
                (Assign "wavestart" (VarExpr "w")
                    (Plus (ARead "wavestart" 
                              (Minus (VarExpr "w") (Value(IntVal 1))))
                          (ARead "wavestart" (VarExpr "w")))),
            Malloc "wavefronts" (VarExpr "nnz") (IntVal 0),
            ForLoop "prev" (D1D (Value(IntVal 1)) (Plus (VarExpr "nnz")
                                                         (Value(IntVal 1))))
                (SeqStmt [
                    AssignVar "p" (Minus (VarExpr "nnz") (VarExpr "prev")),
                    AssignVar "w" (ARead "wave" (VarExpr "p")),
                    Assign "wavestart" (VarExpr "w")
                        (Minus (ARead "wavestart" (VarExpr"w"))
                               (Value(IntVal 1))),
                    Assign "wavefronts"
                        (ARead "wavestart" (VarExpr "w"))
                        (VarExpr "p")
                ])    
    ]
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
        ++ (genHstmt inspecAST 1)
        ++ tab ++ "\n"
        ++ tab ++ "// epilogue to capture outputs\n"
        ++ tab ++ "(*max_wave_ptr) = max_wave;\n"
        ++ tab ++ "(*wavestart_ptr) = wavestart;\n"
        ++ tab ++ "(*wavefronts_ptr) = wavefronts;\n"
        ++ "}\n"
