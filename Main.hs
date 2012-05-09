module Main where

-- (c) Dan Rosén 2012
-- compile with
-- ghc -package ghc Main.hs

import CoreMonad
import CoreSyn
import DynFlags
import FloatOut
import GHC
import GHC.Paths
import HscTypes
import Outputable
import SimplCore
import UniqSupply

import Halt.Trans
import Halt.Lift
import Halt.Conf

import FOL.Pretty

import Control.Monad
import System.Environment

desugar :: FilePath -> IO (ModGuts,[CoreBind])
desugar targetFile =
  defaultErrorHandler defaultLogAction $
    {- defaultCleanupHandler defaultDynFlags $ -} do
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        let dflags' = foldl dopt_set dflags
                            [Opt_CaseMerge
                            ,Opt_FloatIn
                            ,Opt_CSE
                            ,Opt_StaticArgumentTransformation
                            ]
        void $ setSessionDynFlags dflags'
        target <- guessTarget targetFile Nothing
        setTargets [target]
        void $ load LoadAllTargets
        modSum <- getModSummary (mkModuleName targetFile)
        p <- parseModule modSum
        t <- typecheckModule p
        d <- desugarModule t
        -- ^ take that
        let modguts = dm_core_module d
        s <- getSession
        modguts' <- liftIO (core2core s modguts)
        let coreBinds = mg_binds modguts'
            float_switches = FloatOutSwitches
                               { floatOutLambdas = Just 100
                               , floatOutConstants = False
                               , floatOutPartialApplications = False
                               }
        us <- liftIO (mkSplitUniqSupply 'l')
           -- ^ Make a UniqSupply out of thin air. Trying char 'l'
        floatedProg <- liftIO (floatOutwards float_switches dflags' us coreBinds)
        return (modguts',floatedProg)

main :: IO ()
main = do
    file:opts <- getArgs
    let flagged x = when (x `elem` opts)
    (modguts,floated_prog) <- desugar file
    us <- mkSplitUniqSupply 'f'
    let core_binds = mg_binds modguts
        ty_cons    = mg_tcs modguts
        halt_conf  = sanitizeConf $ HaltConf
                        { use_cnf      = "-cnf" `elem` opts
                        , inline_projs = True
                        , use_min      = "-no-min" `notElem` opts
                        , common_min   = "-common-min" `elem` opts
                        }
        ((lifted_prog,msgs_lift),us') = caseLetLift floated_prog us
        (tptp,msgs_trans)             = translate us' halt_conf ty_cons lifted_prog

        printSrc = do
            putStrLn $ "Original file, " ++ file ++ ":\n"
            putStrLn =<< readFile (file ++ ".hs")

        printMsgs msgs = unless (null msgs) $ putStrLn $ unlines msgs

        endl = putStrLn "\n"

        printCore msg core = do
            putStrLn $ msg ++ ":\n"
            mapM_ (printDump . ppr) core
            endl

    flagged ("-src-before") printSrc

    flagged ("-origcore") (printCore "Original core" core_binds)


    flagged ("-lamlift") (printCore "Lambda lifted core" floated_prog)

    flagged ("-dbcaseletlift") (printMsgs msgs_lift)
    flagged ("-caseletlift")   (printCore "Case/let lifted core" lifted_prog)

    flagged ("-src") printSrc

    flagged ("-dbtptp") (printMsgs msgs_trans)
    unless ("-no-tptp" `elem` opts) (endl >> outputTPTP tptp >> endl)
