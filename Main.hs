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
  [file] <- getArgs
  (modguts,floated_prog) <- desugar file
  let core_binds = mg_binds modguts
      ty_cons    = mg_tcs modguts
  putStrLn "************************"
  putStrLn "desugared:\n"
  mapM_ (printDump . ppr) core_binds
  putStrLn "**********************************************"
  putStrLn $ "original file, " ++ file ++ ":\n"
  putStrLn =<< readFile (file ++ ".hs")
  putStrLn "************************"
  putStrLn $ file ++ " lambda-lifted:\n"
  mapM_ (printDump . ppr) floated_prog
  putStrLn "************************"
  us <- mkSplitUniqSupply 'f'
  let (lifted_prog,msgs_lift) = caseLetLift us floated_prog
  putStrLn "************************"
  putStrLn $ file ++ " caselet-lifted:\n"
  unless (null msgs_lift) $ putStrLn $ "msgs:\n" ++ unlines msgs_lift ++ "\n"
  mapM_ (printDump . ppr) lifted_prog
  let (tptp,msgs_trans) = translate ty_cons lifted_prog
  unless (null msgs_trans) $ putStrLn $ "msgs:\n" ++ unlines msgs_trans ++ "\n"
  putStrLn $ "original file, " ++ file ++ ":\n"
  putStrLn =<< readFile (file ++ ".hs")
  putStrLn "tptp:\n"
  outputTPTP tptp
