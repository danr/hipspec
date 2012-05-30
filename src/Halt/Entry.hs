{-# LANGUAGE RecordWildCards #-}
module Halt.Entry where


import BasicTypes
import CoreMonad
import CoreSubst (simpleOptExpr)
import CoreSyn
import DynFlags
import FloatOut
import GHC
import GHC.Paths
import HscTypes
import TysWiredIn
import Outputable
import UniqSupply
import SimplCore

import Halt.Trans
import Halt.Lift
import Halt.Conf
import Halt.Monad
import Halt.FOL.Linearise
import Halt.FOL.Style
import Halt.FOL.Rename

import Contracts.Make
import Contracts.Trans
import Contracts.Types

import Control.Monad
import System.Environment
import System.Exit

data DesugarConf = DesugarConf { debug_float_out :: Bool
                               , core2core_pass  :: Bool
                               }

desugar :: DesugarConf -> FilePath -> IO (ModGuts,DynFlags)
desugar DesugarConf{..} targetFile =
  defaultErrorHandler defaultLogAction $
    {- defaultCleanupHandler defaultDynFlags $ -} do
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        let dflags'
              | debug_float_out = foldl dopt_set dflags [Opt_D_dump_simpl_stats
                                                        ,Opt_D_verbose_core2core]
              | otherwise = dflags

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
        modguts' <- if core2core_pass then liftIO (core2core s modguts)
                                      else return modguts
        return (modguts',dflags')

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

