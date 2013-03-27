{-# LANGUAGE RecordWildCards #-}
module HipSpec.GHC.Entry (execute, module HipSpec.GHC.Types) where

import HipSpec.GHC.Types
import HipSpec.GHC.SigMap
import HipSpec.GHC.MakeSig
import HipSpec.GHC.GetSig
import HipSpec.GHC.Scope
import HipSpec.Params

import Test.QuickSpec.Signature

import CoreMonad
import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
-- import SimplCore
import StaticFlags
import CoreSyn

import Data.Monoid

import Var

import HipSpec.GHC.Delude
import Halo.Shared
import Halo.Unfoldings

import qualified Data.Map as M

import Data.Maybe
import Data.List

import Control.Monad

execute :: Params -> IO EntryResult
execute params@Params{..} = do

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

            binds = fixUnfoldings (mg_binds modguts)

            fix_id :: Id -> Id
            fix_id = fixId binds

        when dump_core $ liftIO $ do
            putStrLn "== INIT CORE =="
            putStrLn $ showOutputable binds

        -- Set the context for evaluation
        setContext $
            [ IIDecl (simpleImportDecl (moduleName (ms_mod mod_sum)))
            , IIDecl (qualifiedImportDecl (mkModuleName "Test.QuickSpec.Signature"))
            , IIDecl (qualifiedImportDecl (mkModuleName "Test.QuickSpec.Prelude"))
            ]
            -- Also include the imports the module is importing
            ++ map (IIDecl . unLoc) (ms_textual_imps mod_sum)

        -- Get everything in scope
        named_things <- getNamedThings fix_id

        let props :: [(Var,CoreExpr)]
            props =
                [ (i,e)
                | (_,AnId i) <- M.toList named_things
                , isPropType i
                , Just e <- [unfolding i]
                ]

        -- Make or get signature
        m_sig <- if auto
            then makeSignature params (map fst props)
            else getSignature (map fst $ M.toList named_things)

        -- Make signature map
        sig_info <- case m_sig of
            Nothing -> return Nothing
            Just sig0 -> do
                let sig = sig0 `mappend` withTests 100
                sig_map <- makeSigMap params sig named_things
                return $ Just SigInfo
                    { sig     = sig
                    , sig_map = sig_map
                    }

        -- Wrapping up
        return EntryResult
            { sig_info   = sig_info
            , core_props = props
            }

qualifiedImportDecl :: ModuleName -> ImportDecl name
qualifiedImportDecl m = (simpleImportDecl m) { ideclQualified = True }

