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
         AssignVar "y" (VRead "testInt"),
         AssignVar "y" (ARead "foo" (VRead "x")),
         AssignVar "y" (Plus (VRead "x") (Value (IntVal 5))),
         AssignVar "y" (Plus (VRead "x") (VRead "z")),
         AssignVar "y" (Minus (VRead "x") (Value (IntVal 5))),
         AssignVar "y" (Minus (VRead "x") (VRead "z")),
         AssignVar "y" (ARead "foo" (Minus (VRead "x") (VRead "z"))),
         AssignVar "y" (ARead "foo" (Plus (VRead "x") (Value (IntVal 4)))),
         AssignVar "y" (Mult (VRead "x") (Value (IntVal 5))),
         AssignVar "y" (Mult (VRead "x") (VRead "z")),
         AssignVar "y" (Divide (VRead "x") (Value (IntVal 5))),
         AssignVar "y" (Divide (VRead "x") (VRead "z")),
         AssignVar "y" (ARead "foo" (Mult (VRead "x") (VRead "z"))),
         AssignVar "y" (ARead "foo" (Divide (VRead "x") (Value (IntVal 4)))),
         AssignVar "y" (ARead "foo" (ARead "bar" (Plus (VRead "x")
                                                      ((Value (IntVal 4)))))),
         AssignVar "testBool" (CmpGTE (VRead "x") 
                     (Minus (Value (IntVal 0)) (Value (IntVal 1)))),
         AssignVar "testBool" (CmpGT (VRead "x") (Value (IntVal 0))),
         AssignVar "testBool" (CmpLTE (VRead "x") (Value (IntVal 0))),
         AssignVar "testBool" (CmpLT (VRead "x") (Value (IntVal 0))),
         AssignVar "y" (Max (VRead "x") (ARead "foo" (VRead "z"))),
         AssignVar "y" 
             (Plus (VRead "sum")
                 (Divide (Value (DoubleVal 1.0))
                     (Exp (Mult (VRead "k") 
                        (Mult (ARead "data_org" (ARead "row" (VRead "p")))
                             (ARead "data_org" (ARead "col" (VRead "p")))))))),
         Assign "lr_iter"
                    (ARead "row" (Minus (VRead "p") (Value(IntVal 1))))
                    (Minus (VRead "p") (Value(IntVal 1))),
         IfStmt  (CmpGTE (ARead "lw_iter" (VRead "r")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VRead "p")
                                (Max (ARead "wave" (VRead "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lw_iter" (VRead "r")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
         IfStmt (CmpLTE (VRead "iter") (Value(IntVal(5))))
                    (SeqStmt [
                         AssignVar "k" (Plus (VRead "k")(Value(IntVal(1)))),
                         AssignVar "flag" (Value(BoolVal False)) ])
                    (SeqStmt [
                         AssignVar "k" (Minus (VRead "k")(Value(IntVal(1)))),
                         AssignVar "flag" (Value(BoolVal True)) ]),
         Malloc "lw_iter" (VRead "N")  (IntVal (-1)),
         Malloc "dArray"  (Plus (VRead "N") (Value(IntVal (-1)))) 
                          (DoubleVal 0.0),
         Malloc "bArray" (VRead "N")  (BoolVal (False)),
         Malloc "b2Array" (VRead "N")  (BoolVal (True)),
         ForLoop "prev" (D1D (Value(IntVal 1)) (Plus (VRead "nnz")
                                                     (Value(IntVal 1))))
                (SeqStmt [
                    AssignVar "p" (Minus (VRead "nnz") (VRead "prev")),
                    AssignVar "w" (ARead "wave" (VRead "p")),
                    Assign "wavestart" (VRead "w")
                        (Minus (ARead "wavestart" (VRead"w"))
                               (Value(IntVal 1))),
                    Assign "wavefronts"
                        (ARead "wavestart" (VRead "w"))
                        (VRead "p")
                ])    




        ]

{-
-- PseudoC representation of find_waves_fast_gen inspector
--findWavesFast :: PseudoC.Stmt
findWavesFast = SeqStmt [
        Malloc "lw_iter" (VRead "N")  (IntVal (-1)),
        Malloc "lr_iter" (VRead "N")  (IntVal (-1)),
        Malloc "wave"    (VRead "nnz") (IntVal 0),
        AssignVar "max_wave" (Value (IntVal 0)),
        ForLoop "p" (D1D (Value(IntVal 1)) (VRead "nnz"))
            (SeqStmt [
                Assign "lr_iter"
                    (ARead "row" (Minus (VRead "p") (Value(IntVal 1))))
                    (Minus (VRead "p") (Value(IntVal 1))),
                Assign "lr_iter"
                    (ARead "col" (Minus (VRead "p") (Value(IntVal 1))))
                    (Minus (VRead "p") (Value(IntVal 1))),
                Assign "lw_iter"
                    (ARead "row" (Minus (VRead "p") (Value(IntVal 1))))
                    (Minus (VRead "p") (Value(IntVal 1))),
                Assign "lw_iter"
                    (ARead "col" (Minus (VRead "p") (Value(IntVal 1))))
                    (Minus (VRead "p") (Value(IntVal 1))),
                AssignVar "r" (ARead "row" (VRead "p")),
                AssignVar "c" (ARead "col" (VRead "p")),
                IfStmt  (CmpGTE (ARead "lw_iter" (VRead "r")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VRead "p")
                                (Max (ARead "wave" (VRead "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lw_iter" (VRead "r")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                IfStmt  (CmpGTE (ARead "lr_iter" (VRead "r")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VRead "p")
                                (Max (ARead "wave" (VRead "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lr_iter" (VRead "r")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                IfStmt  (CmpGTE (ARead "lw_iter" (VRead "c")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VRead "p")
                                (Max (ARead "wave" (VRead "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lw_iter" (VRead "c")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                IfStmt  (CmpGTE (ARead "lr_iter" (VRead "c")) 
                                (Value(IntVal(0))))
                        (Assign "wave" (VRead "p")
                                (Max (ARead "wave" (VRead "p"))
                                     (Plus (ARead "wave"
                                                (ARead "lr_iter" (VRead "c")))
                                           (Value(IntVal(1))))))
                        (SeqStmt []),
                AssignVar "max_wave" (Max (VRead "max_wave")
                                          (ARead "wave" (VRead "p")))
            ]),
            Malloc "wavestart" (Plus (VRead "max_wave") (Value(IntVal 2)))
                                (IntVal 0),
            ForLoop "p" (D1D (Value(IntVal 0)) (VRead "nnz"))
                (Assign "wavestart" (ARead "wave" (VRead "p"))
                    (Plus (ARead "wavestart" (ARead "wave" (VRead "p")))
                          (Value(IntVal 1)))),
            ForLoop "w" (D1D (Value(IntVal 1)) (Plus (VRead "max_wave")
                                                     (Value(IntVal 1))))
                (Assign "wavestart" (VRead "w")
                    (Plus (ARead "wavestart" 
                              (Minus (VRead "w") (Value(IntVal 1))))
                          (ARead "wavestart" (VRead "w")))),
            Malloc "wavefronts" (VRead "nnz") (IntVal 0),
            ForLoop "prev" (D1D (Value(IntVal 1)) (Plus (VRead "nnz")
                                                         (Value(IntVal 1))))
                (SeqStmt [
                    AssignVar "p" (Minus (VRead "nnz") (VRead "prev")),
                    AssignVar "w" (ARead "wave" (VRead "p")),
                    Assign "wavestart" (VRead "w")
                        (Minus (ARead "wavestart" (VRead"w"))
                               (Value(IntVal 1))),
                    Assign "wavefronts"
                        (ARead "wavestart" (VRead "w"))
                        (VRead "p")
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
