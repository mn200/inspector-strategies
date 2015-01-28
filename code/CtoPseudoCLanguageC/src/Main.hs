--module Main (main) where
module Main(main) where
import PseudoC
import CtoPseudoCParser
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

--import IO
--import List
--import Char

data Options = Options  { optVerbose    :: Bool
                        , optInput      :: FilePath --IO String
                        , optSign :: String
                        , optPretty :: CTranslUnit -> IO ()
                        , optPseudoC :: String -> IO ()
                        , optOutput     :: String -> IO () -- CTranslUnit -> IO () --String -> IO ()
                        }
emptyFun f =
      putStrLn "Program Done"

noPseudoC f =
          putStrLn "No Pseudo File to generate"

startOptions :: Options
startOptions = Options  { optVerbose    = False
                        , optInput      = "test.c" --getContents
                        , optSign = "int main()"
                        , optPretty = emptyFun
                        , optPseudoC = noPseudoC           
                        , optOutput     = (putStrLn )
                        }

                
options :: [ OptDescr (Options -> IO Options) ]
options =
    [ Option "i" ["input"]
        (ReqArg
            (\arg opt -> return opt { optInput = arg })
            "FILE")
        "Input file"
 
    , Option "o" ["output"]
        (ReqArg
            (\arg opt -> return opt { optOutput = ((writeFile arg)) })
            "FILE")
        "Output for the C code generated from the PseudoC created from the original C code"
      
    , Option "m" ["signature"]
        (ReqArg
            (\arg opt -> return opt { optSign = arg }) --optOutput = ((writeFile "generated-code-with-sig.c") . (concatSignature arg) . (genCstmtInv 1) . genPseudoC)})
            "SIGNATURE")
        "signature for the generated C code (Ex: int main() )"

    , Option "p" ["prettyPrinting"]
        (NoArg
            (\opt -> return opt { optPretty = printMyAST})) --printMyAST . genC . genPseudoC})) --(writeFile arg) . (render . pretty) })
        "Pretty print the original C code"
      
    , Option "c" ["PseudoCoutput"]
        (ReqArg
            (\arg opt -> return opt { optPseudoC = (writeFile arg) })
            "FILE")
        "Output for the PseudoC created from the original C code"
      
    {-, Option "s" ["string"]
        (ReqArg
            (\arg opt -> return opt { optInput = arg })
            "FILE")
        "Input string"-}
    , Option "v" ["verbose"]
        (NoArg
            (\opt -> return opt { optVerbose = True }))
        "Enable verbose messages"
 
    , Option "V" ["version"]
        (NoArg
            (\_ -> do
                hPutStrLn stderr "Version 0.01"
                exitWith ExitSuccess))
        "Print version"
 
    , Option "h" ["help"]
        (NoArg
            (\_ -> do
    	        prg <- getProgName
                hPutStrLn stderr (usageInfo prg options)
                exitWith ExitSuccess))
        "Show help"
    ]

--main :: IO ()
main = do
    args <- getArgs
 
    -- Parse options, getting a list of option actions
    let (actions, nonOptions, errors) = getOpt RequireOrder options args
 
    -- Here we thread startOptions through all supplied option actions
    opts <- foldl (>>=) (return startOptions) actions
 
    let Options { optVerbose = verbose
                , optInput = input
                , optSign = sign
                , optPretty = pretty
                , optPseudoC = pseudoc
                , optOutput = output   } = opts
 
    when verbose (hPutStrLn stderr "Hello!")
    (parseMyFile input) >>= (output . (genCSig sign) . genPseudoC)
    (parseMyFile input) >>= (pseudoc  . pseudoC2String . genPseudoC)
    (parseMyFile input) >>= pretty
    --(parseMyFile input) >>= (pseudoc. (genCSig sign) . (string2PseudoC)  . pseudoC2String . genPseudoC)
    -- Missing string2PseudoC for bootstrapping
    

construct ::[FilePath] -> IO ()
construct fs =
    ((parseMyFile (head fs)) >>= (printPseudoC . genPseudoC))



