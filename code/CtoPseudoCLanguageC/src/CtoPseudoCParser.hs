--module Main (main) where
module CtoPseudoCParser where
import PseudoC
import Language.C
import Language.C.System.GCC   -- preprocessor used
import System.Environment
import System.Exit
import Text.Groom
import Control.Exception
import System.Console.GetOpt
import System.IO
import Control.Monad
import Text.PrettyPrint.HughesPJ


parseMyFile :: FilePath ->  IO CTranslUnit
parseMyFile input_file =
  do parse_result <- parseCFile (newGCC "gcc") Nothing [] input_file
     case parse_result of
       Left parse_err -> error (show parse_err)
       Right ast      -> return ast

-- dependence on PseudoC Grammar in Haskell.

genPseudoC :: CTranslUnit -> PseudoC.Stmt 
genPseudoC c_ast = case c_ast of
           CTranslUnit a nodeinfo -> genTree a
           _ -> (InitVar "v" (IntVal 1))

printPseudoC :: Stmt -> IO ()
printPseudoC pseudoc =
             (putStrLn . genC) pseudoc


--genTree :: [CDeclExt] -> PseudoC.Stmt            
genTree ll = case ll of
             (a:q) ->  genCExternalDeclaration a
             _ -> (InitVar "v" (IntVal 1))

genCExternalDeclaration a =
  case a of
       CDeclExt (a) -> genCDeclaration a 
       CFDefExt (a) -> genCFunctionDef a
       CAsmExt (a) b -> SeqStmt [ (genCStringLiteral a)]
       _ -> (InitVar "v" (IntVal 2))

genCDeclaration a =
  case a of
       CDecl cDeclarationSpecifier maybe info ->  (genCDeclarationMaybeElmt (head maybe))  --(InitVar "v" (head (map (mapfunc genCDeclarationSpecifier) cDeclarationSpecifier)))

       
genCDeclarationMaybeElmt a =
   case a of
             --Nothing -> IntVal 2
             --Just a -> genCExpression a
             (Just cDeclarator, Nothing, Nothing)-> (genVarOrArrayA (genCDeclarator cDeclarator) (IntVal 0))
             (Just cDeclarator, Just cInitializer, Nothing)->  (genVarOrArray (genCDeclarator cDeclarator) (cInitializer))
             (Just cDeclarator, Just cInitializer, Nothing)->  (genVarOrArray (genCDeclarator cDeclarator) (cInitializer))
             --(Just cDeclarator, Just cInitializer, Just cExpression) -> (InitVar "v" (IntVal 1))
             --(Nothing, Nothing, Just cExpression) -> (InitVar "v" (IntVal 1))
             --(Nothing, Just cInitializer , Just cExpression) -> (InitVar "v" (IntVal 1))
             --(Nothing, Just cInitializer , Nothing) -> (InitVar "v" (IntVal 1))

genVarOrArrayA a b =
  case a of
       Left a -> InitVar a  b
       --Right a -> Malloc a (Value (IntVal (5))) (IntVal (-1))
   
genVarOrArray a b =
  case a of
       Left a -> genCInitializer  a  b
       Right a -> case b of
                       CInitExpr cExpression info	-> Malloc a (genCExpressionExpr cExpression) (IntVal (1)) --Malloc a (Value (IntVal 1))
                       CInitList cInitializerList info -> Empty

genCDeclarator :: CDeclarator a -> Either String String
genCDeclarator a = 
  case a of 
       CDeclr Nothing cDerivedDeclaratorList maybeCStringLiteral  cAttributeList a -> Left("NoName")
       CDeclr (Just ident) ((CPtrDeclr c info1):cDerivedDeclaratorList) maybeCStringLiteral  cAttributeList a -> Right(genIdent ident)  --It is an array
       CDeclr (Just ident) cDerivedDeclaratorList maybeCStringLiteral  cAttributeList a -> Left(genIdent ident) 


genIdent a = identToString a
  
genCInitializer a b =
  case b of
        CInitExpr cExpression info	-> case cExpression of
                                                 CBinary cBinaryOp cExpression1 cExpression2 info -> (SeqStmt ((InitVar a (IntVal 1)):[AssignVar a (genCExpressionExpr (CBinary cBinaryOp cExpression1 cExpression2 info))]))  -- int k =i+k
                                                 _ -> InitVar a (genCExpressionValType cExpression) -- int k=0
        CInitList cInitializerList info -> Empty

genValType a =
  case a of
        Left a -> IntVal 1
        Right b -> b
        
genStmt a =
  case a of
       Left a -> a
       --Right b -> InitVar "v" (IntVal 0)

genCExpressionStmt :: CExpression a -> Stmt
genCExpressionStmt a =
   case a of
        --CComma cExpression a -> 	 Right(IntVal 222)
        CAssign cAssignOp (CIndex cExpression11 cExpression12 info)  cExpression2 a -> Assign  (genCExpressionString cExpression11)  (genCExpressionExpr cExpression12) (genCExpressionExpr cExpression2) -- Array 
        CAssign cAssignOp cExpression1 cExpression2 a -> AssignVar  (genCExpressionString cExpression1) (genCExpressionExpr cExpression2) -- Variable
        --CCond cExpression1 maybeCExpression cExpression2 a ->	Right(IntVal 222)
        CBinary cBinaryOp cExpression1 cExpression2 a	->  InitVar "v" (IntVal 2)	  --Left(SeqStmt[((genCBinaryOp cBinaryOp) (genStmt (genCExpression cExpression1)) (genStmt (genCExpression cExpression2)))])
        --CCast cDeclaration cExpression a->	Right(IntVal 222)
        CUnary CPostIncOp cExpression a	 ->	(AssignVar (genCExpressionString cExpression) (Plus (genCExpressionExpr cExpression) (Value (IntVal 1))))
        -- As you can guess i++ is not possible easily in peusdoC (since we are mixing expr and stmt, and side effect in c)
        -- And I cannot access easily the type of the variable (without keeping a full list of initialzed variable but Intval is going to work for float and int.

        --CUnary cUnaryOp cExpression a	 ->	
        --CSizeofExpr cExpression a	 ->	Right(IntVal 222)
        --CSizeofType cDeclaration a	 ->	Right(IntVal 222)
        --CAlignofExpr cExpression a	 ->	Right(IntVal 222)
        --CAlignofType cDeclaration a	 ->	Right(IntVal 222)
        --CComplexReal cExpression a	 ->	Right(IntVal 222)
        --CComplexImag cExpression a	 ->	Right(IntVal 222)
        --CIndex cExpression1 cExpression2 a->	Right(IntVal 222)	 
        --CCall cExpression cExpressionList a	 ->	Right(IntVal 222)
        --CMember cExpression ident bool a	 ->	Right(IntVal 222)
        --CVar ident a	 ->	Right(IntVal 222)
        --CConst cConstant	-> Right (genCConstant cConstant)
        --CCompoundLit cDeclaration cInitializerList a->	Right(IntVal 222)	
        --CStatExpr cStatement a	->	Right(IntVal 222)
        --CLabAddrExpr ident a	->	Right(IntVal 222)
        --CBuiltinExpr cBuiltinThing->	Right(IntVal 222)

genCExpressionString :: CExpression a -> String
genCExpressionString a =
   case a of
        CComma cExpression a -> "a"
        CAssign cAssignOp cExpression1 cExpression2 a -> 	 "b"
        CCond cExpression1 maybeCExpression cExpression2 a ->	"c"
        CBinary cBinaryOp cExpression1 cExpression2 a	->  "d"
        CCast cDeclaration cExpression a-> "d"
        CUnary CIndOp cExpression a	 -> "(*" ++ (genCExpressionString cExpression) ++ ")"	
        CUnary cUnaryOp cExpression a	 ->  "e"	
        CSizeofExpr cExpression a	 -> "f"	
        CSizeofType cDeclaration a	 -> "g"	
        CAlignofExpr cExpression a	 -> "h"	
        CAlignofType cDeclaration a	 -> "i"
        CComplexReal cExpression a	 -> "j"	
        CComplexImag cExpression a	 -> "k"	
        CIndex cExpression1 cExpression2 a-> "l" --(genCExpressionString cExpression1) ++ "[" ++ (genCExpressionString cExpression2) ++ "]"
        CCall cExpression cExpressionList a	 ->	"m"
        CMember cExpression ident bool a	 ->	"n"
        CVar ident a	 ->	genIdent ident
        CConst cConstant	-> "t"
        CCompoundLit cDeclaration cInitializerList a->	"o"	
        CStatExpr cStatement a	->	"p"
        CLabAddrExpr ident a	->	"q"
        CBuiltinExpr cBuiltinThing->	"r"


genCExpressionValType :: CExpression a -> ValType
genCExpressionValType a =
   case a of
        --CComma cExpression a -> 	 IntVal 1
        --CAssign cAssignOp cExpression1 cExpression2 a -> IntVal 2	 
        --CCond cExpression1 maybeCExpression cExpression2 a ->	IntVal 3
        CBinary cBinaryOp cExpression1 cExpression2 a	-> genCExpressionValType cExpression2	  --Left(SeqStmt[((genCBinaryOp cBinaryOp) (genStmt (genCExpression cExpression1)) (genStmt (genCExpression cExpression2)))])
        --CCast cDeclaration cExpression a->	IntVal 4
        CUnary cUnaryOp cExpression a	 ->	genCExpressionValType cExpression 
        --CSizeofExpr cExpression a	 ->	IntVal 5
        --CSizeofType cDeclaration a	 ->	IntVal 6
        --CAlignofExpr cExpression a	 ->	IntVal 7
        --CAlignofType cDeclaration a	 ->	IntVal 8
        --CComplexReal cExpression a	 ->	IntVal 9
        --CComplexImag cExpression a	 ->	IntVal 10
        --CIndex cExpression1 cExpression2 a->	IntVal 11 
        --CCall cExpression cExpressionList a	 ->	IntVal 12
        --CMember cExpression ident bool a	 ->	IntVal 13
        --CVar ident a	 ->	IntVal 14 -- for i = 0; i<'N' 
        CConst cConstant	-> genCConstant cConstant True
        --CCompoundLit cDeclaration cInitializerList a->	Right(IntVal 222)	
        --CStatExpr cStatement a	->	Right(IntVal 222)
        --CLabAddrExpr ident a	->	Right(IntVal 222)
        --CBuiltinExpr cBuiltinThing->	Right(IntVal 222)
        
genCExpressionExpr :: CExpression a -> Expr
genCExpressionExpr a =
   case a of
        --CComma cExpression a -> 	Value(IntVal 1) 
        --CAssign cAssignOp cExpression1 cExpression2 a -> Value(IntVal 2)
        --CCond cExpression1 maybeCExpression cExpression2 a ->	Value(IntVal 3)
        CBinary cBinaryOp cExpression1 (CSizeofType cExpression2 info) a	->  (genCExpressionExpr cExpression1)
        CBinary cBinaryOp (CSizeofType cExpression1 info) cExpression2 a	->  (genCExpressionExpr cExpression2)
        CBinary cBinaryOp cExpression1 cExpression2 a	->  (genCBinaryOp cBinaryOp) (genCExpressionExpr cExpression1) (genCExpressionExpr cExpression2)
        CCast cDeclaration cExpression a->	genCExpressionExpr cExpression
        CUnary CMinOp (CConst cConstant) a	 -> Value(genCConstant cConstant False) -- -1
        CUnary CPlusOp cExpression a	 -> genCExpressionExpr cExpression -- 1
        --CUnary cUnaryOp cExpression a	 ->Value(IntVal 4)
  
        --CSizeofExpr cExpression a	 ->	Value(IntVal 5)
        --CSizeofType cDeclaration a	 ->	Value(IntVal 6)
        --CAlignofExpr cExpression a	 ->     Value(IntVal 7)	
        --CAlignofType cDeclaration a	 ->	Value(IntVal 8)
        --CComplexReal cExpression a	 ->	Value(IntVal 9)
        --CComplexImag cExpression a	 ->	Value(IntVal 10)
        CIndex cExpression1 cExpression2 a->	ARead (genCExpressionString  cExpression1) (genCExpressionExpr cExpression2)	 -- Reading Array
        CCall cExpression cExpressionList a	 ->	case (genCExpressionString cExpression) of
                                                           "max" -> fmax  (map genCExpressionExpr cExpressionList) --Max (genCExpressionExpr (head cExpressionList)) (genCExpressionExpr (head cExpressionList))--(genCExpressionExpr (head (tail cExpressionList))) --Limited function support
                                                           "min"  -> fmin  (map genCExpressionExpr cExpressionList)
                                                           a ->  VRead a 
        --CMember cExpression ident bool a	 ->	Right(IntVal 222)
        CVar ident a	 ->	VRead (genIdent ident) 
        CConst cConstant	-> Value (genCConstant cConstant True)
        --CCompoundLit cDeclaration cInitializerList a->	Right(IntVal 222)	
        --CStatExpr cStatement a	->	Right(IntVal 222)
        --CLabAddrExpr ident a	->	Right(IntVal 222)
        --CBuiltinExpr cBuiltinThing->	Right(IntVal 222)

fmax  l =
  case l of
       a:[]-> a
       a:q -> Max a (fmax q)

fmin  l =
  case l of
       a:[]-> a
       a:q -> Min a (fmin q)
       
-- |The 'square' function squares an integer.
genCExpressionExprLeft :: CExpression a -> Expr
genCExpressionExprLeft a =
   case a of
        --CComma cExpression a -> 	 Right(IntVal 222)
        --CAssign cAssignOp cExpression1 cExpression2 a -> 	 
        --CCond cExpression1 maybeCExpression cExpression2 a ->	Right(IntVal 222)
        --CBinary cBinaryOp cExpression1 (CSizeofType cExpression2 info) a	->  (genCExpressionExpr cExpression2)
        CBinary cBinaryOp (CSizeofType cExpression1 info) cExpression2 a	->  (genCExpressionExpr cExpression2)
        CBinary cBinaryOp cExpression1 cExpression2 a	->   (genCExpressionExpr cExpression2)
        --CCast cDeclaration cExpression a->	genCExpressionExpr cExpression
        --CUnary cUnaryOp cExpression a	 ->	Right(IntVal 222)
        --CSizeofExpr cExpression a	 ->	Right(IntVal 222)
        --CSizeofType cDeclaration a	 ->	Value(IntVal 1)
        --CAlignofExpr cExpression a	 ->	Right(IntVal 222)
        --CAlignofType cDeclaration a	 ->	Right(IntVal 222)
        --CComplexReal cExpression a	 ->	Right(IntVal 222)
        --CComplexImag cExpression a	 ->	Right(IntVal 222)
        --CIndex cExpression1 cExpression2 a->	Right(IntVal 222)	 
        --CCall cExpression cExpressionList a	 ->	genCExpressionExpr (head cExpressionList)
        --CMember cExpression ident bool a	 ->	Right(IntVal 222)
        --CVar ident a	 ->	VRead (genIdent ident) 
        --CConst cConstant	-> Value (genCConstant cConstant)
        --CCompoundLit cDeclaration cInitializerList a->	Right(IntVal 222)	
        --CStatExpr cStatement a	->	Right(IntVal 222)
        --CLabAddrExpr ident a	->	Right(IntVal 222)
        --CBuiltinExpr cBuiltinThing->	Right(IntVal 222)



genCBinaryOp a =
  case a of
       CMulOp -> Mult	 
       CDivOp -> Divide	 
       --CRmdOp -> Mult	
       CAddOp -> Plus 
       CSubOp -> Minus	 
       --CShlOp -> Mult	
       --CShrOp -> Mult	
       CLeOp -> CmpLT	
       --CGrOp -> Mult	
       --CLeqOp -> Mult	
       CGeqOp -> CmpGTE	
       --CEqOp -> Mult	
       --CNeqOp -> Mult	
       --CAndOp -> Mult	
       --CXorOp -> Mult	
       --COrOp -> Mult	
       --CLndOp -> Mult	
       --CLorOp -> Mult	

genCConstant a f=
  case a of
       CIntConst cInteger a-> if f
                                 then IntVal (fromInteger (getCInteger cInteger))
                                 else IntVal (-fromInteger (getCInteger cInteger))
       CCharConst cChar a->IntVal 222	 
       CFloatConst (CFloat str) a-> DoubleVal (read str :: Double)
       CStrConst cString a-> IntVal 222


genCDeclarationSpecifier a =
  case a of
       --CStorageSpec cStorageSpecifier -> 
       CTypeSpec cTypeSpecifier -> genCTypeSpecifier cTypeSpecifier
       --CTypeQual cTypeQualifier -> 

genCTypeSpecifier a =
  case a of
       --CVoidType a -> 
      -- CCharType a ->  
       --CShortType a-> 	 
       CIntType a-> (IntVal 0)	 
       --CLongType a-> 	 
       --CFloatType a-> 	 
       CDoubleType a-> (DoubleVal 0)	 
       --CSignedType a->
       --CUnsigType a-> 
       CBoolType a-> (BoolVal True)	 
       --CComplexType a	->  
       --CSUType (CStructureUnion a) a	-> (InitVar "v" (IntVal 16))
       --CEnumType (CEnumeration a) a	-> (InitVar "v" (IntVal 16))
       --CTypeDef Ident a	-> (InitVar "v" (IntVal 16))
       --CTypeOfExpr (CExpression a) a	-> (InitVar "v" (IntVal 16))
       --CTypeOfType (CDeclaration a) a	-> (InitVar "v" (IntVal 16))


genCFunctionDef a =
  case a of
       CFunDef a b c d e -> genCStatement d

genCStatement a =
  case a of
   --CLabel v stmt attr a	-> (InitVar "v" (IntVal 7))
   CCase expr stmt a -> IfStmt (genCExpressionExpr expr) (genCStatement stmt) (Empty)
   --CCases expr1 expr2 stmt a -> IfStmt (genCExpressionExpr expr1) (genCStatement stmt) (Empty)		
   CDefault stmt a -> (genCStatement stmt)
   --CExpr (Nothing) a	-> (InitVar "v" (IntVal 10))
   CExpr (Just cExpression) a	->  (genCExpressionStmt cExpression)
   CCompound varlist cCompoundBlockItemlist a-> SeqStmt (map (mapfunc genCCompound) cCompoundBlockItemlist)
   CIf expr stmt Nothing a	-> IfStmt (genCExpressionExpr expr) (genCStatement stmt) (Empty)
   CIf expr stmt (Just stmt2) a	-> IfStmt (genCExpressionExpr expr) (genCStatement stmt) (genCStatement stmt2) 
   CSwitch expr stmt a-> (genCStatementInCase expr stmt)
   CWhile expr stmt bool a	-> WhileLoop (genCExpressionExpr expr) (genCStatement stmt)
   --CFor eitherMaybeCExpressionCDeclaration maybeCExpression1 Nothing cStatement a	-> ForLoop "A" (D1D (Value(IntVal 0)) (Value (IntVal 5))) (genCStatement cStatement)
   --CFor eitherMaybeCExpressionCDeclaration maybeCExpression1 Nothing cStatement a	-> ForLoop "B" (D1D (Value(IntVal 0)) (Value (IntVal 5))) (genCStatement cStatement)
   --CFor (Left Nothing) maybeCExpression1 (Just cExpression2) cStatement a	-> ForLoop "D" (D1D (Value(IntVal 0)) (Value (IntVal 5))) (genCStatement cStatement)
   --CFor (Left (Just cExpression)) maybeCExpression1 (Just cExpression2) cStatement a	-> ForLoop (genCExpressionString cExpression) (D1D (Value(IntVal 0)) (Value (IntVal 5))) (genCStatement cStatement)
   CFor (Right cDeclaration) (Just cExpression1) (Just cExpression2) cStatement a	-> (SeqStmt (Empty:((ForLoop (getIdCDeclaration cDeclaration)   (D1D (getValueCDeclaration cDeclaration) (genCExpressionExprLeft cExpression1)) (genCStatement cStatement))):[])) --(Value (genCExpressionValType cExpression1))) (genCStatement cStatement))):[]))
   --CFor (Right cDeclaration) Nothing (Just cExpression2) cStatement a	-> (SeqStmt (Empty:((ForLoop (getIdCDeclaration cDeclaration)   (D1D (getValueCDeclaration cDeclaration) (Value (IntVal(0)))) (genCStatement cStatement))):[])) 
     {-CGoto Ident a	->(InitVar "v" (IntVal 3))
  CGotoPtr (CExpression a) a	->(InitVar "v" (IntVal 3))
  CCont a	->(InitVar "v" (IntVal 3))-}
   CBreak a-> Empty
{-  CReturn (Maybe (CExpression a)) a->(InitVar "v" (IntVal 3))	
  CAsm (CAssemblyStatement a) a	->(InitVar "v" (IntVal 3))
-}

genCStatementInCase exprE stmt =
  case stmt of
       CCase expr stmt a -> IfStmt (CmpLT (genCExpressionExpr exprE) (genCExpressionExpr expr)) (genCStatement stmt) (Empty)
       CDefault stmt a -> (genCStatement stmt)
       CCompound varlist cCompoundBlockItemlist a-> SeqStmt (map (mapfunc (genCCompoundInCase exprE)) cCompoundBlockItemlist)
       CBreak a-> Empty

genCCompoundInCase exprE stmt =
  case stmt of
       CBlockDecl b -> genCDeclaration b
       CBlockStmt cStatement ->  genCStatementInCase exprE cStatement
       --_ -> (InitVar "v" (IntVal 6))

-- Used for FORLOOP
getIdCDeclaration a =
  case a of
       CDecl cDeclarationSpecifier l info ->  case (head l) of
                                                        (Just cDeclarator, Nothing, Nothing)->  case (genCDeclarator cDeclarator) of
                                                                                                               Left a -> a
                                                                                                               Right a -> "a"
                                                        (Just cDeclarator, Just cInitializer, Nothing)->  case (genCDeclarator cDeclarator) of
                                                                                                               Left a -> a
                                                                                                               Right a -> "b"
                                                        (Just cDeclarator, Just cInitializer, Nothing)->  case (genCDeclarator cDeclarator) of
                                                                                                               Left a -> a
                                                                                                               Right a -> "c"
                                                        (Just cDeclarator, Just cInitializer, Just cExpression) ->  case (genCDeclarator cDeclarator) of
                                                                                                               Left a -> a
                                                                                                               Right a -> "d"
                                                        (Nothing, Nothing, Just cExpression) -> "e"
                                                        (Nothing, Just cInitializer , Just cExpression) -> "f"
                                                        (Nothing, Just cInitializer , Nothing) -> "g"

-- Need to be int/double/bool
getValueCDeclaration a =
  case a of
       CDecl cDeclarationSpecifier l info ->  case (head l) of
                                                        (Just cDeclarator, Nothing, Nothing)-> Value(IntVal 0)
                                                        (Just cDeclarator, Just cInitializer, Nothing)->  case cInitializer of
                                                                                                           CInitExpr cExpression info -> Value (genCExpressionValType cExpression)
                                                        (Just cDeclarator, Just cInitializer, Nothing)-> case cInitializer of
                                                                                                           CInitExpr cExpression info -> Value (genCExpressionValType cExpression)
                                                        (Just cDeclarator, Just cInitializer, Just cExpression) ->case cInitializer of
                                                                                                           CInitExpr cExpression info -> Value (genCExpressionValType cExpression)
                                                        (Nothing, Nothing, Just cExpression) -> Value(IntVal 0)
                                                        (Nothing, Just cInitializer , Just cExpression) -> case cInitializer of
                                                                                                           CInitExpr cExpression info -> Value (genCExpressionValType cExpression)
                                                        (Nothing, Just cInitializer , Nothing) ->            case cInitializer of
                                                                                                           CInitExpr cExpression info -> Value (genCExpressionValType cExpression)                    

mapfunc f c =
  f c

genCCompound a =
  case a of
       CBlockDecl b -> genCDeclaration b
       CBlockStmt cStatement ->  genCStatement cStatement
       _ -> (InitVar "v" (IntVal 6))

genCStringLiteral a =
  case a of
       CStrLit a b-> (InitVar "v" (IntVal 5))
  
printMyAST :: CTranslUnit -> IO ()
--printMyAST :: CTranslUnit -> String
printMyAST ctu = putStrLn(groom ctu)
