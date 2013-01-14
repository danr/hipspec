{-# LANGUAGE RecordWildCards, CPP #-}
{-

    A main entry point to Halo, called `desugar', even though it can
    run the GHC core-to-core passes as well, and return the TypeEnv.
    The latter is used to get the "built-in" classes such as Eq, Ord
    and Monad.

-}
module Halo.Entry where

import CoreMonad
import CoreSubst (simpleOptExpr)
import CoreSyn
import DynFlags
import FloatOut
import GHC
import GHC.Paths
import HscTypes
import SimplCore
import StaticFlags
import TcRnTypes
import UniqSupply

import Halo.Util

import Data.List
import Data.Maybe
import Data.IORef

import Control.Monad

data DesugarConf = DesugarConf
    { debug_float_out :: Bool
    , core2core_pass  :: Bool
    }

desugar :: DesugarConf -> FilePath -> IO (ModGuts,DynFlags)
desugar dc fp = first fst <$> desugarAndTypeEnv dc fp

desugarAndTypeEnv :: DesugarConf -> FilePath -> IO ((ModGuts,TypeEnv),DynFlags)
desugarAndTypeEnv DesugarConf{..} targetFile =
#if __GLASGOW_HASKELL__ >= 706
  defaultErrorHandler defaultFatalMessager defaultFlushOut $
#else
  defaultErrorHandler defaultLogAction $
#endif
    {- defaultCleanupHandler defaultDynFlags $ -} do
      addWay WayThreaded
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        let dflags0
                | debug_float_out = foldl dopt_set dflags
                                        [Opt_D_dump_simpl_stats
                                        ,Opt_D_verbose_core2core]
                | otherwise = dflags
            dflags' = (flip dopt_unset Opt_IgnoreInterfacePragmas
                     $ flip dopt_unset Opt_OmitInterfacePragmas
                     $ dopt_set dflags0 Opt_ExposeAllUnfoldings)
        void $ setSessionDynFlags dflags'
        target <- guessTarget targetFile Nothing
        setTargets [target]
        void $ load LoadAllTargets
        mod_graph <- getModuleGraph
        let mod_sum = fromMaybe (error $ "Cannot find module " ++ targetFile)
                    $ find (\m -> ms_mod_name m == mkModuleName targetFile
                               || ms_mod_name m == mkModuleName "Main"
                               || ml_hs_file (ms_location m) == Just targetFile)
                           mod_graph
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t
        let modguts = dm_core_module d
        s <- getSession
        modguts' <- if core2core_pass
                        then liftIO (core2core s modguts)
                        else return modguts
        type_env <- liftIO . readIORef . tcg_type_env_var . fst . tm_internals_ $ t
        return ((modguts',type_env),dflags')

lambdaLift :: DynFlags -> CoreProgram -> IO CoreProgram
lambdaLift dflags program = do
    us <- mkSplitUniqSupply 'l'
    floatOutwards float_switches dflags us (map simpleOpt program)
  where
    simpleOpt (NonRec v e) = NonRec v (simpleOptExpr e)
    simpleOpt (Rec vses)   = Rec [ (v,simpleOptExpr e) | (v,e) <- vses ]

    float_switches = FloatOutSwitches
        { floatOutLambdas = Just 100
        , floatOutConstants = False
        , floatOutPartialApplications = True
        }
