module Main where


main::IO()
main = do 
        putStrLn (genWaveInspector "find_waves_fast_gen")
        putStrLn (genWaveInspector "rauchwerger95")
        putStrLn (genWaveInspector "zhuang09")
        
tab :: String
tab = "    "

-- Given the inspector function name and AST generate the C inspector function.
-- Generates the stub needed by wavebench-driver.cpp.
genWaveInspector :: String -> String
genWaveInspector inspecName = "void " ++ inspecName 
        ++ "(COO_mat *mat, int nnz, int * row, int *col,\n"
        ++ tab ++ tab ++ "int *max_wave_ptr, int **wavestart_ptr,\n"
        ++ tab ++ tab ++ "int **wavefronts_ptr) {\n"
        ++ tab ++ "int max_wave = 0;\n"
        ++ tab ++ "int* wavestart=(int*)calloc((max_wave+2),sizeof(int));\n"
        ++ tab ++ "int *wavefronts=(int*)malloc(sizeof(int)*nnz);\n"
        ++ tab ++ "\n"
        ++ tab ++ "// epilogue to capture outputs\n"
        ++ tab ++ "(*max_wave_ptr) = max_wave;\n"
        ++ tab ++ "(*wavestart_ptr) = wavestart;\n"
        ++ tab ++ "(*wavefronts_ptr) = wavefronts;\n"
        ++ "}\n"
