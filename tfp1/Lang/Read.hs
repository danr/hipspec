module Lang.Read where

import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
import StaticFlags
import CoreSyn

import UniqSupply
import Data.IORef
import GhcMonad

import SimplCore

import Lang.Unfoldings
import Lang.RemoveDefault
import Lang.Uniquify

import Data.Maybe
import Data.List

import Control.Monad
import Control.Applicative

{-# ANN module "HLint: ignore Use camelCase" #-}

data Optimise = Optimise | Don'tOptimise

readBinds :: Optimise -> FilePath -> IO [CoreBind]
readBinds opt file = do

    -- Use -threaded
    addWay WayThreaded

    -- Notify where ghc is installed
    runGhc (Just libdir) $ do

        -- Set interpreted so we can get the signature,
        -- and expose all unfoldings
        dflags0 <- getSessionDynFlags
        let dflags = dflags0 { ghcMode = CompManager
                             , optLevel = 1
                             , profAuto = NoProfAuto
                             }
                `dopt_unset` Opt_IgnoreInterfacePragmas
                `dopt_unset` Opt_OmitInterfacePragmas
                `dopt_set` Opt_ExposeAllUnfoldings
        _ <- setSessionDynFlags dflags

        -- Try to get the target
        let file' | ".hs" `isSuffixOf` file = take (length file - 3) file
                  | otherwise               = file

        target <- guessTarget (file' ++ ".hs") Nothing
        _ <- addTarget target
        r <- load LoadAllTargets
        when (failed r) $ error "Compilation failed!"

        mod_graph <- getModuleGraph
        let mod_sum = fromMaybe (error $ "Cannot find module " ++ file')
                    $ find (\m -> ms_mod_name m == mkModuleName file'
                               || ms_mod_name m == mkModuleName (replace '/' '.' file')
                               || ms_mod_name m == mkModuleName "Main"
                               || ml_hs_file (ms_location m) == Just file')
                           mod_graph
              where replace a b = map (\ x -> if x == a then b else x)

        -- Parse, typecheck and desugar the module
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t

        modguts <- case opt of
            Optimise ->  do
                -- Get the session so we can use core2core optimise
                hsc_env <- getSession
                -- Get the modguts (and optimise it)
                liftIO (core2core hsc_env (dm_core_module d))
            Don'tOptimise -> return (dm_core_module d)

        binds <- ghcRunUniqSM $
            (runUQ . mapM (`uqBind` return) <=< removeDefaults)
            (mg_binds modguts)

        return (fixUnfoldings binds)

ghcRunUniqSM :: UniqSM a -> Ghc a
ghcRunUniqSM m = do
    nc_ref <- hsc_NC <$> getSession
    nc <- liftIO $ readIORef nc_ref
    let (a,us') = initUs (nsUniqs nc) m
    liftIO $ writeIORef nc_ref (nc { nsUniqs = us' })
    return a

