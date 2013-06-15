{-# LANGUAGE RecordWildCards #-}
module Read where

import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
import StaticFlags
import CoreSyn

import Unfoldings

import Data.Maybe
import Data.List

import Control.Monad

readBinds :: FilePath -> IO [CoreBind]
readBinds file = do

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
              where replace a b xs = map (\ x -> if x == a then b else x) xs

        -- Parse, typecheck and desugar the module
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t

        let modguts = dm_core_module d

        return (fixUnfoldings (mg_binds modguts))

