
{
module Main where

import Data.Char
import PseudoC

}

%name c2pseudoc
%tokentype { Token }
%error { parseError }

%token 
      let             { TokenLet }
      in              { TokenIn }
      if              { TokenIf }
      else            { TokenElse }
      for             { TokenFor }
      intkw           { TokenIntkw }
      int             { TokenInt $$ }
      boolkw          { TokenBoolkw }
      bool            { TokenBool $$ }
      doublekw        { TokenDoublekw }
      expkw           { TokenExpkw }
      maxkw           { TokenMaxkw }
      malloc          { TokenMalloc }
      sizeof          { TokenSizeof }
      gte             { TokenGte }
      lt              { TokenLt }
      var             { TokenVar $$ }
      pp              { TokenPP }
      '='             { TokenEq }
      '+'             { TokenPlus }
      '-'             { TokenMinus }
      '*'             { TokenTimes }
      '/'             { TokenDiv }
      '('             { TokenOB }
      ')'             { TokenCB }
      ';'             { TokenSemi }
      ','             { TokenComma }
      '['             { TokenOSB }
      ']'             { TokenCSB }
      '{'             { TokenObrack }
      '}'             { TokenCbrack }


%left       gte lt
%left       '+' '-' 
%left       '*' '/'


%%
Stmts
      : Stmt                          { $1 }
      | Stmts Stmt                    { $1++$2 }

Stmt  
      : ScalarType var '=' Expr ';'   { [DeclVar $1 $2, AssignVar $2 $4] }
      | ScalarType var ';'            { [DeclVar $1 $2] }
      | var '=' Expr ';'              { [AssignVar $1 $3] }
      | var '[' Expr ']' '=' Expr ';' { [Assign $1 $3 $6] }
      | if '(' Expr ')' Stmt else Stmt
                                      { [IfStmt $3 (SeqStmt $5) (SeqStmt $7)] }
      | '{' Stmts '}'                 { $2 }
      | for '(' intkw var '=' Expr ';' var lt Expr ';' var pp ')' Stmt
                                      { [ForLoop $4 (D1D $6 $10) (SeqStmt $15)] }
      | intkw '*' var '=' malloc '(' sizeof '(' intkw ')' '*' Expr ')' ';' 
        for '(' intkw var '=' Expr ';' var lt Expr ';' var pp ')' 
                var '[' var ']' '=' int ';'
                                      { [Malloc $3 $12 (IntVal $34)] }
      | boolkw '*' var '=' malloc '(' sizeof '(' boolkw ')' '*' Expr ')' ';' 
        for '(' intkw var '=' Expr ';' var lt Expr ';' var pp ')' 
                var '[' var ']' '=' bool ';'
                                      { [Malloc $3 $12 (BoolVal $34)] }
--      | doublekw '*' var '=' malloc '(' sizeof '(' doublekw ')' '*' Expr ')' ';' 
--        for '(' intkw var '=' Expr ';' var lt Expr ';' var pp ')' 
--                var '[' var ']' '=' double ';'
--                                      { [Malloc $3 $12 (DoubleVal $34)] }


                                           

Expr  : Expr gte Expr                 { (CmpGTE $1 $3) }
      | Expr lt Expr                  { (CmpLT $1 $3) }
      | Expr '+' Expr                 { (Plus $1 $3) } 
      | Expr '-' Expr                 { (Minus $1 $3) }
      | Expr '*' Expr                 { (Mult $1 $3) }
      | Expr '/' Expr                 { (Divide $1 $3) }
      | expkw '(' Expr ')'            { (Exp $3) }
      | maxkw '(' Expr ',' Expr ')'   { (Max $3 $5) }
      | var '[' Expr ']'              { (ARead $1 $3) }
      | int                           { (Value (IntVal $1)) }
      | bool                          { (Value (BoolVal $1)) }
      | var                           { (VarExpr $1) }
--      | double                        { (Value (DoubleVal $1)) }

Type  : ScalarType                    { $1 }
      | VectorType                    { $1 }

ScalarType
      : intkw                         { "int" }
      | boolkw                        { "bool" }
      | doublekw                      { "double" }
      
VectorType
      : intkw '*'                     { "int *" }
      | boolkw '*'                    { "bool *" }
      | doublekw '*'                  { "double *" }
      
{

parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
      = TokenLet
      | TokenIn
      | TokenIf
      | TokenElse
      | TokenFor
      | TokenIntkw
      | TokenInt Int
      | TokenBoolkw
      | TokenBool Bool
      | TokenDoublekw
      | TokenExpkw
      | TokenMaxkw
      | TokenMalloc
      | TokenSizeof
      | TokenVar String
      | TokenGte
      | TokenLt
      | TokenEq
      | TokenPP
      | TokenPlus
      | TokenMinus
      | TokenTimes
      | TokenDiv
      | TokenOB
      | TokenCB
      | TokenOSB
      | TokenCSB
      | TokenObrack
      | TokenCbrack
      | TokenSemi
      | TokenComma
      deriving Show


lexer :: String -> [Token]
lexer [] = []
lexer (c:cs) 
      | isSpace c = lexer cs
      | isAlpha c = lexVar (c:cs)
      | isDigit c = lexNum (c:cs)
lexer ('>':'=':cs) = TokenGte : lexer cs      
lexer ('<':cs) = TokenLt : lexer cs
lexer ('+':'+':cs) = TokenPP : lexer cs
lexer ('=':cs) = TokenEq : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenMinus : lexer cs
lexer ('*':cs) = TokenTimes : lexer cs
lexer ('/':cs) = TokenDiv : lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer ('[':cs) = TokenOSB : lexer cs
lexer (']':cs) = TokenCSB : lexer cs
lexer ('{':cs) = TokenObrack : lexer cs
lexer ('}':cs) = TokenCbrack : lexer cs
lexer (';':cs) = TokenSemi : lexer cs
lexer (',':cs) = TokenComma : lexer cs

lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
   case span isAlpha cs of
      ("let",rest)  -> TokenLet : lexer rest
      ("int",rest)  -> TokenIntkw : lexer rest
      ("bool",rest) -> TokenBoolkw : lexer rest
      ("double",rest) -> TokenDoublekw : lexer rest
      ("true",rest) -> TokenBool True : lexer rest
      ("false",rest) -> TokenBool False : lexer rest
      ("in",rest)   -> TokenIn : lexer rest
      ("if",rest)   -> TokenIf : lexer rest
      ("else",rest) -> TokenElse : lexer rest
      ("for",rest)  -> TokenFor : lexer rest
      ("exp",rest)  -> TokenExpkw : lexer rest
      ("MAX",rest)  -> TokenMaxkw : lexer rest
      ("malloc",rest) -> TokenMalloc : lexer rest
      ("sizeof",rest) -> TokenSizeof : lexer rest
      (var,rest)    -> TokenVar var : lexer rest

main = getContents >>= print . c2pseudoc . lexer
}
