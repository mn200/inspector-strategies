module Main where
import PseudoC
import Language.C
import Language.C.System.GCC   -- preprocessor used
import System.Environment
import System.Exit
import Text.Groom


main :: IO ()
main = (getArgs >>= parseArgs)

parseArgs :: [[Char]] -> IO ()
parseArgs ["-h"] = usage   >> exit
parseArgs ["-v"] = version >> exit
parseArgs [] = usage   >> exit
parseArgs ["-p"]= exit
parseArgs fs     = (putStrLn (PseudoC.genCstmt (genPseudoC (parseMyFile (head fs))) 0))
                   --  (head fs)) >>= printMyAST))

usage :: IO ()
usage   = putStrLn "Usage: CPseudoCLanguageC [-vhp] [C file]"
version :: IO ()
version = putStrLn "C to PseudoC 0.1"
exit :: IO a
exit    = exitWith ExitSuccess
die :: IO a
die     = exitWith (ExitFailure 1)

parseMyFile :: FilePath -> IO CTranslUnit
parseMyFile input_file =
  do parse_result <- parseCFile (newGCC "gcc") Nothing [] input_file
     case parse_result of
       Left parse_err -> error (show parse_err)
       Right ast      -> return ast

-- dependence on PseudoC Grammar in Haskell.

genPseudoC :: IO CTranslUnit -> PseudoC.Stmt 
genPseudoC c_ast = case c_ast of
           _ -> AssignVar "v" (Value (IntVal 1)) 
             
       
printMyAST :: CTranslUnit -> IO ()
--printMyAST :: CTranslUnit -> String
printMyAST ctu = putStrLn(groom ctu)
