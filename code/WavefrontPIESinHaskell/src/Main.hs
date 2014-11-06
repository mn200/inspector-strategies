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
        putStrLn (genWaveZhuang09Inspector "zhuang09"  zhuang09)
        
tab :: String
tab = "    "

-- stub inspector that just mallocs and sets minimal vars for C compile
stub :: PseudoC.Stmt
stub = SeqStmt
        [InitVar "max_wave" (IntVal(0)),
         Malloc "wavestart" 
                (Plus (VRead("max_wave")) (Value (IntVal(2))))
                (IntVal 0),
         Malloc "wavefronts" (VRead("nnz")) (IntVal 0)
-- instructions below for testing additional functionality
-- in PseudoC.hs not currently in wavebench
{-
         ,
         InitVar "testBool" (BoolVal (False)),
         InitVar "testDouble" (DoubleVal 0.0),
         Malloc "testBarray" (VRead("nnz")) (BoolVal (True)),
         Malloc "testDarray" (VRead("nnz")) (DoubleVal (-1.0)),
         WhileLoop (CmpLT (VRead "max_wave") (Value(IntVal(5))))
                   (AssignVar "max_wave" 
                              (Mult (Value(IntVal(10)))
                                    (Divide (VRead "max_wave")
                                            (Value(IntVal(2))))))
-}
        ]

-- The wavefront computation is for the moment algorithm dependant
-- For the moment: sparse matrix multiplication
{-
            int i = row[p];
            int j = col[p];
            if (debug) {
                printf("executor: i=%d, j=%d\n", i, j);
            }
            // sum = Sum_{k=0}^{w-1} 1 / exp( k * data[i] * data[j] )
            double sum = 0.0;
            for (int k=0; k<workPerIter; k++) {
                sum += 1.0 / exp( (double)k * data[i] * data[j] );
            }
            data[ i ] += 1.0 + sum;
            data[ j ] += 1.0 + sum;
        }
-}
-- Read pos. = Write pos.



-- PseudoC representation of find_waves_fast_gen inspector
findWavesFast :: PseudoC.Stmt
findWavesFast = SeqStmt [
        Malloc "lw_iter" (VRead "N")  (IntVal (-1)),
        Malloc "lr_iter" (VRead "N")  (IntVal (-1)),
        Malloc "wave"    (VRead "nnz") (IntVal 0),
        InitVar "max_wave" (IntVal 0),
        InitVar "r" (IntVal(0)),
        InitVar "c" (IntVal(0)),
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
            InitVar "p" (IntVal(0)),
            InitVar "w" (IntVal(0)),
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


-- PseudoC representation of zhaung09 inspector (our reading of it)
-- http://dx.doi.org/10.1109/PACT.2009.10
-- Exploiting Parallelism with Dependence-Aware Scheduling
{- for each inspector thread t:
     for all x, lastwrite(x) = lastread(x) = lbi(t)-1;
     for all i in lbi(t) to ubi(t), DDA(i) = i;

     // loop over rest of loop domain
     for (i=lbi(t) to ubi(t)) { // order matters

         reduction loop (i,x) in W_A {
             DDA(i) = min( DDA(i), i - max( lastwrite(x), lastread(x) ) );
         }
 
         reduction loop (i,x) in R_A { 
             DDA(i) = min( DDA(i), i-lastwrite(x));
         }

 
        foreach (i,x) in W_A { 
             lastwrite(x) = i
        }
 
        foreach (i,x) in R_A { 
             lastread(x) = i
        }
}-}

zhuang09 :: PseudoC.Stmt
zhuang09 = SeqStmt [
  Inline "int tid = 0;\n",
  --Comment "lr/w_iter are private, DDA;wave;wavestart;wavefronts are shared",
  --InitVar "nb_threads" (IntVal 2),
  Inline "int nb_threads= atoi(getenv (\"OMP_NUM_THREADS\"));\n", -- Dont really need nb_threads var.
  Malloc "DDA" (VRead "nnz") (IntVal(-1)),
  InitVar "max_wave" (IntVal 0),
  Malloc "wave"    (VRead "nnz")       (IntVal 0),
  -- nb_threads must divide nnz
  Inline "if(nnz % nb_threads != 0) { printf (\"nb_threads needs to divide nnz: %d\\n\",nnz);exit;}",
  PrintVar "nb_threads",
  Comment "Should be parallelized with more argument",
  ParForLoop "t" (D1D (Value(IntVal 1)) (Plus (VRead "nb_threads") (Value (IntVal 1))))
    (SeqStmt [
        Inline "tid = omp_get_thread_num();\n",
        Comment "nnz is divided by nb_threads",
        InitVar "lbi" (IntVal (0)),
        AssignVar "lbi" (Mult (Divide (VRead "nnz") (VRead "nb_threads")) (Minus (VRead "t") (Value (IntVal 1)))),
        InitVar "ubi" (IntVal (0)),
        AssignVar "ubi" (Minus (Mult (Divide (VRead "nnz") (VRead "nb_threads")) (VRead "t")) (Value (IntVal 1))),
        
        Malloc "lw_iter" (VRead "nnz")  (IntVal(-1)),

        Malloc "lr_iter" (VRead "nnz") (IntVal (-1)), -- Malloc need a value type
        PrintVar "lbi",
        PrintVar "ubi",
        PrintArray "lr_iter" (VRead "nnz"),
        Comment "The reason for two loops to have a initialization is that Malloc only takes Valtype (in Haskell)",
        ForLoop "i" (D1D (Value(IntVal 0)) (VRead "nnz"))
            (SeqStmt [
                     Assign "lr_iter"
                            (VRead "i")
                            (Minus (VRead "lbi") (Value(IntVal(1)))),
                     Assign "lw_iter"
                            (VRead "i")
                            (Minus (VRead "lbi") (Value(IntVal(1))))
                     ]
            )
        ,
        --Malloc "DDA" (Plus (ARead "lbi" (VRead "t")) (Plus (ARead "ubi" (VRead "t")) (Value(IntVal(1))))) ((IntVal(1))),
        Comment "DDA will be shared among inspectors threads but each section is accesed only by one processus",
        ForLoop "i" (D1D (VRead "lbi") (Plus (VRead "ubi") (Value(IntVal(1)))))
            (SeqStmt [
                     Assign "DDA"
                            (VRead "i")
                            (Plus (VRead "i") (Value(IntVal(1))))
                     ]
            )
        ,       
        InitVar "r" (IntVal(0)),
        InitVar "c" (IntVal(0)),
        Comment "Will be sequential. But there is several threads that are computing the dep.",
        ForLoop "p" (D1D (VRead "lbi") (Plus (VRead "ubi") (Value(IntVal(1)))))
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
                PrintVar "c",
                PrintVar "r",        
                PrintArray "lr_iter" (VRead "nnz"),
                PrintArray "lw_iter" (VRead "nnz"),
                 Assign "DDA"
                            (VRead "p")
                            (Min (ARead "DDA" (VRead "p")) (Minus (Plus (VRead "p") (Value(IntVal(1)))) (Plus (Value (IntVal 1)) (Max (Max (ARead "lr_iter" (VRead "c")) (ARead "lw_iter" (VRead "c"))) (Max (ARead "lr_iter" (VRead "r")) (ARead "lw_iter" (VRead "r"))))))),

                 PrintArray "DDA" (VRead "nnz"),
                 Assign "wave" (VRead "p") (Minus (Plus (VRead "p") (Value (IntVal(1)))) (ARead "DDA" (VRead "p"))),
                 PrintArray "wave" (VRead "nnz"),
                 {-,
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
                        (SeqStmt []), -}
                AssignVar "max_wave" (Max (VRead "max_wave")
                                          (ARead "wave" (VRead "p")))   
                ])]),
            Comment "wavefront is an index function mapping iterations inside a wavefront to the real iterations",
            Comment "wavestart is indicating the starting iteration of the wavefront = wavestart[wavefront[w]]",
            Malloc "wavestart" (Plus (VRead "max_wave") (Value(IntVal 2)))
                                (IntVal 0),
            ForLoop "p" (D1D (Value(IntVal 0)) (VRead "nnz"))
                (Assign "wavestart" (ARead "wave" (VRead "p"))
                    (Plus (ARead "wavestart" (ARead "wave" (VRead "p")))
                          (Value(IntVal 1)))),
            ForLoop "w" (D1D (Value(IntVal 1)) (Plus (VRead "max_wave")
                                                     (Value(IntVal 2))))
                (Assign "wavestart" (VRead "w")
                    (Plus (ARead "wavestart" 
                              (Minus (VRead "w") (Value(IntVal 1))))
                          (ARead "wavestart" (VRead "w")))),
            Malloc "wavefronts" (VRead "nnz") (IntVal 0),
            InitVar "p" (IntVal(0)),
            InitVar "w" (IntVal(0)),
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
                ]),
            --Comment "t=1, then start of the array",
            --IfStmt  (CmpGTE (VRead "t") (Value (IntVal(1))))
                        --(IfStmt  (CmpLT (VRead "t") (Value (IntVal(2))))
                   --             (SeqStmt [
              --                      AssignVar "*wavestart_ptr" (VRead "wavestart"),
                 --                   AssignVar "*wavefronts_ptr" (VRead "wavefronts")])
                                           --(SeqStmt []))
   --                     (SeqStmt [])
     
   -- ,--]),
    PrintArray "DDA" (VRead "nnz"),
    PrintVar "max_wave"--,
    --Inline "for (w=0;w<max_wave;w++){for (int i=0;i<nnz;i++){if(wave[wavefronts[i]] == w){printf(\"Iteration %d belong the wavefront %d\\n\",i,w);}}}"
  ]

-- Given the inspector function name and AST generate the C inspector function.
-- Generates the stub needed by wavebench-driver.cpp.
-- FIXME: might want to move into PseudoC since have C code.
genWaveInspector :: String -> PseudoC.Stmt -> String
genWaveInspector inspecName inspecAST =
        "void " ++ inspecName 
        ++ "(COO_mat *mat, int nnz, int * row, int *col,\n"
        ++ tab ++ tab ++ "int *max_wave_ptr, int **wavestart_ptr, int **wavefronts_ptr) {\n"
        ++ (genCstmt inspecAST 1)
        ++ tab ++ "\n"
        ++ tab ++ "// epilogue to capture outputs\n"
        ++ tab ++ "(*max_wave_ptr) = max_wave;\n"
        ++ tab ++ "(*wavestart_ptr) = wavestart;\n"
        ++ tab ++ "(*wavefronts_ptr) = wavefronts;\n"
        ++ "}\n"


-- Given the inspector function name and AST generate the C inspector function.
-- Generates the stub needed by wavebench-driver.cpp.
-- FIXME: might want to move into PseudoC since have C code.
genWaveZhuang09Inspector :: String -> PseudoC.Stmt -> String
genWaveZhuang09Inspector inspecName inspecAST =
        "void " ++ inspecName 
        ++ "(COO_mat *mat, int nnz, int * row, int *col,\n"
        ++ tab ++ tab ++ "int *max_wave_ptr, int **wavestart_ptr,\n"
        ++ tab ++ tab ++"int **wavefronts_ptr) {\n \n"
        ++ (genCstmt inspecAST 1)
        ++ tab ++ "\n"
        ++ tab ++ "// epilogue to capture outputs\n"
        ++ tab ++ "(*max_wave_ptr) = max_wave;\n"
        ++ tab ++ "(*wavestart_ptr) = wavestart;\n"
        ++ tab ++ "(*wavefronts_ptr) = wavefronts;\n"
        ++ "}\n"

{-genWaveQuarkInspector :: String -> PseudoC.Stmt -> String
genWaveQuarkInspector inspecName inspecAST =
        "void " ++ inspecName 
        ++ "(COO_mat *mat, int nnz, int * row, int *col,\n"
        ++ tab ++ tab ++ "int *max_wave_ptr, int **wavestart_ptr,\n"
        ++ tab ++ tab ++ "int **wavefronts_ptr) {\n"
        ++ (genQuarkstmt inspecAST 1)
        ++ tab ++ "\n"
        ++ tab ++ "// epilogue to capture outputs\n"
        ++ tab ++ "(*max_wave_ptr) = max_wave;\n"
        ++ tab ++ "(*wavestart_ptr) = wavestart;\n"
        ++ tab ++ "(*wavefronts_ptr) = wavefronts;\n"
        ++ "}\n"-}
