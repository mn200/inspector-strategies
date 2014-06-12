-- PseudoC AST

module PseudoC where

data ValType = 
          IntVal Int 
        | BoolVal Bool
        deriving (Show)

data Expr =
          Value ValType
        | VarExpr String
        
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
        deriving (Show)
        
data Domain =
         D1D Expr Expr
         deriving (Show)


data Stmt =
         -- Array element definition (array name, index exp, and rhs)
           Assign String Expr Expr

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

         -- Statement sequencing
         -- Named different than Seq because somewhat different.
         -- Seq in HOL stuff is instance of body for sequential loop.
         | SeqStmt [Stmt]
         
         deriving (Show)

-- C code generation functions.

genCexpr :: Expr -> String
genCexpr (Value (IntVal n)) = show n
genCexpr (Value (BoolVal b)) = show b
genCexpr (VarExpr var) = var
genCexpr (Plus e1 e2) = "("++(genCexpr e1)++" + "++(genCexpr e2)++")"

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
        (AssignVar var rhs) -> (indent lvl) ++ "int " ++ var
                               ++ " = " ++ (genCexpr rhs) ++ ";\n"
                                 
        -- Generate malloc call and initialization loop.
        (Malloc var sz (IntVal(n))) -> (indent lvl)++"int* "++var
            ++" = (int*)malloc(sizeof(int)*"++(genCexpr sz)++");\n"
            ++(genCstmt 
                (ForLoop "i" (D1D (Value(IntVal(0))) sz)
                    (Assign var (VarExpr "i") (Value(IntVal(n)))) )
            lvl)
            
        (ForLoop iter (D1D lb ub) body) ->
            (indent lvl)++"for (int "++iter++"="++(genCexpr lb)++"; "
            ++iter++"<"++(genCexpr ub)++"; "++iter++"++) {\n"
            ++(genCstmt body (lvl+1))
            ++(indent lvl)++"}\n"

        (SeqStmt ([]))-> ""
        (SeqStmt (x:xs)) -> (genCstmt x lvl)++(genCstmt (SeqStmt xs) lvl)


{-|
(* lvl specifies the current tab level, should usually start at 0 *)
fun genCstmt ast lvl =
    (* 4 spaces of indentation per level *)
    let fun indent lvl = if lvl>0 then "    "^(indent (lvl-1)) else ""
    in
        case ast of
            Assign(id,idx,rhs) =>
            (indent lvl) ^ id^"["^(genCexpr idx)^"] = "^(genCexpr rhs)^";\n"

          | AssignVar(var,rhs) =>
            (indent lvl) ^ var^" = "^(genCexpr rhs)^";\n"

          | IfStmt(e,thenbody,elsebody) =>
            (indent lvl) ^"if ("^(genCexpr e)^") {\n"
            ^(genCstmt thenbody (lvl+1))
            ^(genCstmt elsebody (lvl+1))
            ^(indent lvl)^"}\n"

          (* FIXME: output init code *)                               
          | Malloc(id,sz,Int(n)) =>
            (indent lvl) ^ id^" = (int*)malloc(sizeof(int)*"
            ^(genCexpr sz)
            ^");\n"

          | ForLoop(iter,D1D(lb,ub),body) =>
            (indent lvl) ^"for (int "^iter^"=("^(genCexpr lb)^"); "
            ^iter^"<("^(genCexpr ub)^"); "^iter^"++) {\n"
            ^(genCstmt body (lvl+1))
            ^(indent lvl) ^"}\n"

          | ParForLoop(iter,D1D(lb,ub),body) =>
            (indent lvl) ^"#pragma omp parallel for\n"
            ^(indent lvl) ^"for (int "^iter^"=("^(genCexpr lb)^"); "
            ^iter^"<("^(genCexpr ub)^"); "^iter^"++) {\n"
            ^(genCstmt body (lvl+1))
            ^(indent lvl) ^"}\n"

         | SeqStmt(s::slist) =>
           (genCstmt s lvl)^(genCstmt (SeqStmt(slist)) lvl)

         | SeqStmt([]) => "" 

    end
-}
