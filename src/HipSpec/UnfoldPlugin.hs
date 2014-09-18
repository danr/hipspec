module HipSpec.UnfoldPlugin (plugin) where

import HipSpec.GHC.Unfoldings
import HipSpec.GHC.Utils
import CoreMonad
import CoreSyn

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _args todos = do
  liftIO $ putStrLn "HELLO!?"
  reinitializeGlobals
  putMsgS "Hello from HipSpec.UnfoldPlugin"
  return $ todos ++ [CoreDoPluginPass "UnfoldPlugin" (bindsOnlyPass unf)] --  (return . fixUnfoldings))]

unf :: [CoreBind] -> CoreM [CoreBind]
unf cb = do
    let cb' = fixUnfoldings cb
    liftIO $ putStrLn (showOutputable cb')
    return cb'
