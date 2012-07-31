{-

    An attempt to use the case-let-lifter as a GHC plugin.

-}
module Halo.LiftPlugin where

import CoreMonad
import DynFlags
import FloatOut
import GHC
import GHC.Paths
import GhcPlugins

import Halo.Lift

plugin :: Plugin
plugin = defaultPlugin {
    installCoreToDos = insertLiftToDo
  }

insertLiftToDo :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
insertLiftToDo _ todo = do
   reinitializeGlobals
   return (CoreDoPluginPass "liftPass" liftPass : todo)

liftPass :: ModGuts -> CoreM ModGuts
liftPass = bindsOnlyPass $ \binds -> do
    us1 <- getUniqueSupplyM
    dflags <- getDynFlags
    let float_switches = FloatOutSwitches
                           { floatOutLambdas = Just 100
                           , floatOutConstants = False
                           , floatOutPartialApplications = False
                           }
    lambda_lifted_binds <- liftIO (floatOutwards float_switches dflags us1 binds)
    us2 <- getUniqueSupplyM
    return $ fst $ caseLetLift us2 lambda_lifted_binds

