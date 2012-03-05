-- (c) Dan Rosén 2012
-- compile with
-- ghc -package ghc Main.hs

import GHC
import Outputable
import GHC.Paths
import DynFlags
import HscTypes
import SimplCore

import Halt.Trans
import FOL.Pretty

import System.Environment

desugar :: FilePath -> IO ModGuts
desugar targetFile =
  defaultErrorHandler defaultDynFlags $ do
    runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      let dflags' = foldl dopt_set (foldl xopt_set dflags
                          [Opt_Cpp, Opt_MagicHash])
                          [Opt_FloatIn,Opt_CSE,Opt_DoEtaReduction
                          ,Opt_CaseMerge,Opt_StaticArgumentTransformation
                          ,Opt_FullLaziness]
      setSessionDynFlags dflags'
      target <- guessTarget targetFile Nothing
      setTargets [target]
      load LoadAllTargets
      modSum <- getModSummary $ mkModuleName "CoreTest"
      p <- parseModule modSum
      t <- typecheckModule p
      d <- desugarModule t
      let modguts = dm_core_module d
      withSession (\m -> liftIO (core2core m modguts))
--      return (dm_core_module d)

main = do
  [file] <- getArgs
  modguts <- desugar file
  let coreBinds = mg_binds modguts
  mapM_ (printDump . ppr) coreBinds
  outputTPTP (translate coreBinds)