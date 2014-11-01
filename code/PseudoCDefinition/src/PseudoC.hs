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
        | CmpGTE Expr Expr
        | CmpLT Expr Expr
        deriving (Show)
        
data Domain =
         D1D Expr Expr
         deriving (Show)


data Stmt =
         -- Nop
           Empty
         -- Array element definition (array name, index exp, and rhs)
         |  Assign String Expr Expr

         -- InitVar (declaration plus initialization) to scalar (* var initval *)
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
                  
-- Print Pseudo Code
pseudoC2String :: Stmt -> String
pseudoC2String pseudoc =
               pseudoC2Stringstmt pseudoc 0
               
pseudoC2Stringexpr :: Expr -> String
pseudoC2Stringexpr (Value vtype) = "(Value " ++ (pseudoC2Stringvalue vtype) ++ ")"
pseudoC2Stringexpr (VRead var) = "(VRead "++ var ++ ")"
pseudoC2Stringexpr (ARead var idx) = "(ARead " ++var++ " " ++ (pseudoC2Stringexpr idx)++")"
pseudoC2Stringexpr (Max e1 e2) = "(Max "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"
pseudoC2Stringexpr (Plus e1 e2) = "(Plus "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"
pseudoC2Stringexpr (Minus e1 e2) = "(Minus "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"
pseudoC2Stringexpr (Mult e1 e2) = "(Mult "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"
pseudoC2Stringexpr (Divide e1 e2) = "(Divide "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"
pseudoC2Stringexpr (CmpGTE e1 e2) = "(CmpGTE "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"
pseudoC2Stringexpr (CmpLT e1 e2) = "(CmpLT "++(pseudoC2Stringexpr e1)++(pseudoC2Stringexpr e2)++")"


pseudoC2Stringstmt :: Stmt -> Int -> String
pseudoC2Stringstmt s lvl =
  let indent lvl | lvl>0 = "    "++(indent (lvl-1)) | otherwise = ""
    in case s of
        (Empty) -> ""
        (Assign var idx rhs) -> "(Assign " ++ var ++
                                " " ++ (pseudoC2Stringexpr idx) ++ " " 
                                ++ (pseudoC2Stringexpr rhs) ++")"

        (InitVar var initvtype) -> "(InitVar "++ var ++ " " 
                                ++ (pseudoC2Stringvalue initvtype) ++ ")"

        (AssignVar var rhs) -> "(AssignVar "++var++" "++ (pseudoC2Stringexpr rhs)++")"

        (IfStmt e thenbody elsebody) -> "(IfStmt "++(pseudoC2Stringexpr e)++ " "++(pseudoC2Stringstmt thenbody (lvl+1))++ " "++ (pseudoC2Stringstmt  elsebody (lvl+1))++")"

        (Malloc var sz initvtype) -> "(Malloc "++ var++ " "++ (pseudoC2Stringexpr sz) ++ " " ++(pseudoC2Stringvalue initvtype)++")"
                        
        (ForLoop iter (D1D lb ub) body) -> "(ForLoop "++iter++" (D1D "++(pseudoC2Stringexpr lb)++(pseudoC2Stringexpr ub)++") "++(pseudoC2Stringstmt body (lvl+1))++")"

        (WhileLoop e body) -> "(WhileLoop "++(pseudoC2Stringexpr e)++" "++(pseudoC2Stringstmt body (lvl+1))++")"

        (SeqStmt ([]))-> "(SeqStmt ([]))"
        (SeqStmt (x:xs)) -> "(SeqStmt ("++(pseudoC2Stringstmt x (lvl+1)) ++ ":" ++ (pseudoC2Stringstmt (SeqStmt xs) (lvl+1))++"))"

pseudoC2Stringvalue :: ValType -> String
pseudoC2Stringvalue (IntVal (n)) = "(IntVal("++show n++"))"
pseudoC2Stringvalue (DoubleVal (d)) = "(DoubleVal ("++show d++"))"
pseudoC2Stringvalue (BoolVal (b)) = "(BoolVal (" ++show b++ "))"

-- Generate PseudoC from String
string2PseudoC :: String -> Stmt
string2PseudoC str =
               Empty

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
genCexpr (CmpGTE e1 e2) = "("++(genCexpr e1)++")>=("++(genCexpr e2)++")"
genCexpr (CmpLT e1 e2) = "("++(genCexpr e1)++")<("++(genCexpr e2)++")"

genC :: Stmt -> String
genC s =
     genCstmt s 0
genCSig :: String -> Stmt  -> String 
genCSig sig pseudoc =
          sig ++ "{\n" ++ (genCstmt pseudoc 1) ++ "}\n" 
          
genCstmtInv lvl s =
     genCstmt s lvl

-- Given a PseudoC AST, a list of scalar vars that have already
-- declared in the generated C code, and the current tab level
-- generate a string of C code.
genCstmt :: Stmt -> Int -> String
genCstmt s lvl =
    let indent lvl | lvl>0 = "    "++(indent (lvl-1)) | otherwise = ""
    in case s of
        (Empty) -> ""
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
            ++(indent lvl)++"}else {\n"
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

