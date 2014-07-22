-- PseudoC AST

module PseudoC where

data ValType = 
          IntVal Int 
        | BoolVal Bool
        | DoubleVal Double
        deriving (Show)

data Expr =
          Value ValType
        | VRead String
        
        -- array read, e.g., f(i)
        | ARead String Expr
        
        -- operations needed for wavebench example
        | Plus Expr Expr
        | Minus Expr Expr
        | Max Expr Expr
        | Mult Expr Expr
        | Divide Expr Expr
        | Exp Expr          -- exponent function
        | Convert Expr      -- convert integer to double
        
        -- comparison expressions
        | CmpGT Expr Expr
        | CmpGTE Expr Expr
        | CmpLT Expr Expr
        | CmpLTE Expr Expr
--        | CmpEQ Expr Expr -- not yet available in PseudoCOpsScript.sml
        deriving (Show)
        
data Domain =
         D1D Expr Expr
         deriving (Show)


data Stmt =
         -- Array element definition (array name, index exp, and rhs)
           Assign String Expr Expr

         -- InitVar (declaration and initialization) to scalar (* var initval *)
         -- initval is not an expression so can easily get type info
         | InitVar String ValType

         -- Assignment to scalar (* var = rhs *)
         | AssignVar String Expr

         -- If-the-else statement
         | IfStmt Expr Stmt Stmt

         -- Aname, size expression, initval
         -- initval is not an expression so can easily get type info
         | Malloc String Expr ValType

         -- for ( lb <= i < ub ) body
         -- one string for one iterator
         | ForLoop String Domain Stmt

         -- iterations of loop can be executed concurrently
         -- for ( lb <= i < ub ) body
         | ParForLoop String Domain Stmt

         -- while loops cannot be used in the original code
         -- while loops cannot be used in the executor
         | WhileLoop Expr Stmt

         -- Statement sequencing
         -- Named different than Seq because somewhat different.
         -- Seq in HOL stuff is instance of body for sequential loop.
         | SeqStmt [Stmt]
         
         deriving (Show)

--------------------------------------------------------------------------
-- hol code generation functions.

genHexpr :: Expr -> String

genHexpr (Value vtype) = "(Value " ++ (genHvalue vtype) ++ ")"
genHexpr (VRead var) = "(VRead \""++var++"\")"
genHexpr (ARead var idx) = "(ARead \""++var++"\" "++(genHexpr idx)++")"
genHexpr (Plus e1 e2) =  "(Opn plusval [" ++(genHexpr e1)++";"
                                          ++(genHexpr e2)++"])"
genHexpr (Minus e1 e2) = "(Opn minusval ["++(genHexpr e1)++";"
                                          ++(genHexpr e2)++"])"
genHexpr (Mult e1 e2) =   "(Opn multval ["++(genHexpr e1)++";"
                                          ++(genHexpr e2)++"])"
genHexpr (Divide e1 e2) = "(Opn divval [" ++(genHexpr e1)++";"
                                          ++(genHexpr e2)++"])"
genHexpr (CmpGT e1 e2) =  "(Opn cmpGTval ["  ++(genHexpr e1)++";"
                                             ++(genHexpr e2)++"])"
genHexpr (CmpGTE e1 e2) = "(Opn cmpGTEval [" ++(genHexpr e1)++";"
                                             ++(genHexpr e2)++"])"
genHexpr (CmpLT e1 e2) =  "(Opn cmpLTval ["  ++(genHexpr e1)++";"
                                             ++(genHexpr e2)++"])"
genHexpr (CmpLTE e1 e2) = "(Opn cmpLTEval [" ++(genHexpr e1)++";"
                                             ++(genHexpr e2)++"])"
-- -- CmpEQ not yet available in public/hol/pseudoc/PseudoCOpsScript.sml
--genHexpr (CmpEQ e1 e2) =  "(Omp cmpEQval ["  ++(genHexpr e1)++";"
--                                             ++(genHexpr e2)++"])"
genHexpr (Max e1 e2) =    "(Opn maxval [" ++(genHexpr e1)++";"
                                          ++(genHexpr e2)++"])"
genHexpr (Exp e) =        "(Opn expval ["++(genHexpr e)++"])"


-- Given a PseudoC AST, a list of scalar vars that have already
-- declared in the generated hol code, and the current tab level
-- generate a string of hol code.
genHstmt :: Stmt -> Int -> String
genHstmt s lvl =
    let indent lvl | lvl>0 = "    "++(indent (lvl-1)) | otherwise = ""
    in case s of
        (AssignVar var rhs) -> 
            let (cnt, deps, parms, func) = (findDexpr rhs (0,"",""))
            in (indent lvl) ++ "(AssignVar \"" ++ var ++ "\"\n" 
                ++ (indent (lvl+1)) ++ "[" ++ deps ++ "] \n"
                ++ (indent (lvl+1)) ++ "(\\xs . case xs of ["
                ++ parms ++ "] => " ++ func ++"))"

        (Assign var idx rhs) -> 
            let (cnt, deps, parms, func) = (findDexpr rhs (0,"",""))
            in (indent lvl) ++ "(Assign\n"
                ++ (indent (lvl+1)) ++"(\"" ++ var ++ "\",\n" 
                ++ (indent (lvl+1)) ++ (genHexpr idx) ++ ")\n" 
                ++ (indent (lvl+1)) ++ "[" ++ deps ++ "]\n"
                ++ (indent (lvl+1)) ++ "(\\xs . case xs of ["
                ++ parms ++ "] => " ++ func ++"))"

        (IfStmt e thenbody elsebody) -> 
            (indent lvl)++"(IfStmt "
            ++(genHexpr e)++"\n"      -- each genHexpr has it's own ( )
            ++(genHstmt thenbody (lvl+1))++"\n"
            ++(genHstmt elsebody (lvl+1))++")"


        -- Generate malloc call and initialization loop.
        (Malloc var sz initvtype) -> 
            (indent lvl) ++ "(Malloc \"" ++ var ++ "\"\n" 
            ++(indent (lvl+1)) ++ (genHexpr sz) ++ "\n"
            ++(indent (lvl+1)) ++ (genHvalue initvtype) ++ ")"

        (ForLoop iter (D1D lb ub) body) ->
            (indent lvl) ++ "(ForLoop \"" ++ iter ++ "\"\n"
            ++(indent (lvl+1)) ++ "(D " ++ (genHexpr lb) ++ " "
            ++(genHexpr ub) ++ ")\n"
            ++(genHstmt body (lvl+1)) ++ ")"

        (ParForLoop iter (D1D lb ub) body) ->
            (indent lvl) ++ "(ParLoop \"" ++ iter ++ "\"\n"
            ++(indent (lvl+1)) ++ "(D " ++ (genHexpr lb) ++ " "
            ++(genHexpr ub) ++ ")\n"
            ++(genHstmt body (lvl+1)) ++ ")"

-- -- WhileLoop not yet available in public/hol/pseudoc/PseudoCScript.sml
{-
        (WhileLoop e body) ->
            (indent lvl)++"(WhileLoop " ++ (genHexpr e) ++ "\n"
            ++(genHstmt body (lvl+1)) ++ ")"
-}
        (SeqStmt ([]))-> (indent lvl) ++ "(Seq [])"
        (SeqStmt (ys))-> (indent lvl) ++"(Seq [\n" 
                         ++ (genHstmtList ys (lvl+1)) ++"\n"
                         ++ (indent lvl) ++ "])"
            where
               genHstmtList :: [Stmt] -> Int -> String
               genHstmtList (x:xs) llvl =
                  case xs of
                     ([]) -> (genHstmt x llvl)
                     _    -> (genHstmt x llvl) ++ ";\n"
                              ++ (genHstmtList xs llvl)


-- Find the depString, parameterString, and functionString from
--      the rhs of assignment statement
-- usage:  findDexpr Expr (cnt, depString, parameterString)
--   will return (cnt, depString, parameterString, functionString)
-- 
findDexpr :: Expr -> (Int, String, String) -> (Int, String, String, String)
findDexpr (Value vtype) (cnt,deps,parms) = 
                 (cnt, deps, parms, (genHvalue vtype))
findDexpr (VRead var) (cnt,deps,parms) =
              let parm = "x"++(show cnt) 
                  dep = "DVRead \"" ++ var ++ "\""
                  newdeps = case deps of
                      "" -> dep
                      _  -> deps ++ ";" ++ dep
                  newparms = case parms of
                      "" -> parm
                      _  -> parms ++ ";" ++ parm
                  newfunc = parm
              in  (cnt+1, newdeps, newparms, newfunc)

findDexpr (ARead var idx) (cnt,deps,parms) = 
              let parm = "x"++(show cnt) 
                  dep = "D"++(stripParen (genHexpr (ARead var idx)))
                  newdeps = case deps of
                      "" -> dep
                      _  -> deps ++ ";" ++ dep
                  newparms = case parms of
                      "" -> parm
                      _  -> parms ++ ";" ++ parm
                  newfunc = parm
              in  (cnt+1, newdeps, newparms, newfunc)

findDexpr (Plus e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" + ",e1,e2,cnt,deps,parms)
findDexpr (Minus e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" - ",e1,e2,cnt,deps,parms)
findDexpr (Mult e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" * ",e1,e2,cnt,deps,parms)
findDexpr (Divide e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" / ",e1,e2,cnt,deps,parms)
findDexpr (CmpGT e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" > ",e1,e2,cnt,deps,parms)
findDexpr (CmpGTE e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" >= ",e1,e2,cnt,deps,parms)
findDexpr (CmpLT e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" < ",e1,e2,cnt,deps,parms)
findDexpr (CmpLTE e1 e2) (cnt,deps,parms) = 
              getDexprBinOp(" <= ",e1,e2,cnt,deps,parms)
findDexpr (Max e1 e2) (cnt,deps,parms) = 
              let (c1,d1,p1,f1) = (findDexpr e1 (cnt,deps,parms))
                  (c2,d2,p2,f2) = (findDexpr e2 (c1,d1,p1))
              in (c2,d2,p2,"(maxval [" ++ f1 ++ ";" ++ f2 ++ "])" ) 
findDexpr (Exp e) (cnt,deps,parms) = 
              let (c1,d1,p1,f1) = (findDexpr e (cnt,deps,parms))
              in (c1,d1,p1,"(exp " ++ f1 ++ ")" ) 

-- first parameter String is the infix operator for the BinOp
-- (infixop, e1, e2, cnt, deps, params) -> (newcnt, newdep, newparam, funcstr)
getDexprBinOp :: (String, Expr, Expr, Int, String, String) -> 
                       (Int, String, String, String)
getDexprBinOp (infixop, e1, e2, cnt, deps, parms) =
              let (c1,d1,p1,f1) = (findDexpr e1 (cnt,deps,parms))
                  (c2,d2,p2,f2) = (findDexpr e2 (c1,d1,p1))
              in (c2,d2,p2,"(" ++ f1 ++ infixop ++ f2 ++ ")" ) 

-- CmpEQ not yet available in public/hol/pseudoc/PseudoCOpsScript.sml
{-
findDexpr (CmpEQ e1 e2) (cnt,deps,parms) = 
              let (c1,d1,p1,f1) = (findDexpr e1 (cnt,deps,parms))
                  (c2,d2,p2,f2) = (findDexpr e2 (c1,d1,p1))
              in (c2,d2,p2,"(" ++ f1 ++ " == " ++ f2 ++ ")" ) 
-}

stripParen :: String -> String
stripParen str = if (length str) > 1 
                    then if (head str) == '('
                            then if (last str) ==')'
                                   then (tail (init str))
                                   else str
                            else str
                    else str
 
genHvalue :: ValType -> String
genHvalue (IntVal (n)) = "(Int ("++(show n)++"))"
genHvalue (DoubleVal (d)) = "(Real ("++(show d)++"))" 
genHvalue (BoolVal (b)) = genHboolVal b
            where genHboolVal True = "(Bool T)"
                  genHboolVal False = "(Bool F)"

genHtypeString :: ValType -> String
genHtypeString (IntVal(n)) = "Int"
genHtypeString (BoolVal(b)) = "Bool"
genHtypeString (DoubleVal(d)) = "Real"

        

--------------------------------------------------------------------------
-- C code generation functions.

genCexpr :: Expr -> String
genCexpr (Value vtype) = (genCvalue vtype)
genCexpr (VRead var) = var
genCexpr (ARead var idx) = var++"["++(genCexpr idx)++"]"
genCexpr (Max e1 e2) = "MAX("++(genCexpr e1)++", "++(genCexpr e2)++")"
genCexpr (Plus e1 e2) = "("++(genCexpr e1)++" + "++(genCexpr e2)++")"
genCexpr (Minus e1 e2) = "("++(genCexpr e1)++" - "++(genCexpr e2)++")"
genCexpr (Mult e1 e2) = "("++(genCexpr e1)++" * "++(genCexpr e2)++")"
genCexpr (Divide e1 e2) = "("++(genCexpr e1)++" / "++(genCexpr e2)++")"
genCexpr (CmpGTE e1 e2) = "("++(genCexpr e1)++") >= ("++(genCexpr e2)++")"
genCexpr (CmpLT e1 e2) = "("++(genCexpr e1)++") < ("++(genCexpr e2)++")"

-- Given a PseudoC AST, a list of scalar vars that have already
-- declared in the generated C code, and the current tab level
-- generate a string of C code.
genCstmt :: Stmt -> Int -> String
genCstmt s lvl =
    let indent lvl | lvl>0 = "    "++(indent (lvl-1)) | otherwise = ""
    in case s of
        (Assign var idx rhs) -> (indent lvl) ++ var 
                                ++ "[" ++ (genCexpr idx) ++ "] = "
                                ++ (genCexpr rhs) ++ ";\n"
-- Keep track of which vars have been declared.
        (InitVar var initvtype) -> (indent lvl) ++ (genCtypeString initvtype)
                                ++ " " ++ var ++ " = " 
                                ++ (genCvalue initvtype) ++ ";\n"

        (AssignVar var rhs) -> (indent lvl) ++ var
                               ++ " = " ++ (genCexpr rhs) ++ ";\n"
                                 
        (IfStmt e thenbody elsebody) -> (indent lvl)++"if ("
            ++(genCexpr e)++") {\n"
            ++(genCstmt thenbody (lvl+1))
            ++(genCstmt elsebody (lvl+1))
            ++(indent lvl)++"}\n"

        -- Generate malloc call and initialization loop.
        (Malloc var sz initvtype) -> 
            let typestr = (genCtypeString initvtype)
            in  (indent lvl) ++ typestr 
                  ++ "* " ++ var
                  ++ " = (" ++ typestr ++ "*)malloc(sizeof("
                  ++ typestr ++ ")*" ++ (genCexpr sz) ++");\n"
                  ++(genCstmt 
                      (ForLoop "i" (D1D (Value(IntVal(0))) sz)
                          (Assign var (VRead "i") (Value (initvtype)) ))
                  lvl)
                        
        (ForLoop iter (D1D lb ub) body) ->
            (indent lvl)++"for (int "++iter++"="++(genCexpr lb)++"; "
            ++iter++"<"++(genCexpr ub)++"; "++iter++"++) {\n"
            ++(genCstmt body (lvl+1))
            ++(indent lvl)++"}\n"

        (WhileLoop e body) ->
            (indent lvl)++"while ("++(genCexpr e)++") {\n"
            ++(genCstmt body (lvl+1))
            ++(indent lvl)++"}\n"

        (SeqStmt ([]))-> ""
        (SeqStmt (x:xs)) -> (genCstmt x lvl)++(genCstmt (SeqStmt xs) lvl)

genCvalue :: ValType -> String
genCvalue (IntVal (n)) = show n
genCvalue (DoubleVal (d)) = show d 
genCvalue (BoolVal (b)) = genCboolVal b
            where genCboolVal True = "true"
                  genCboolVal False = "false"

genCtypeString :: ValType -> String
genCtypeString (IntVal(n)) = "int"
genCtypeString (BoolVal(b)) = "bool"
genCtypeString (DoubleVal(d)) = "double"

