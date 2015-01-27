-- | Gets the GHC Core information we need, also obtains or creates the
--   QuickSpec signature
{-# LANGUAGE RecordWildCards, NamedFieldPuns, CPP #-}
module HipSpec.Read (execute,EntryResult(..),SigInfo(..)) where

import QuickSpec.Signature (Signature, renumber)

import HipSpec.ParseDSL

import Data.List.Split (splitOn)

import HipSpec.Sig.Resolve
import HipSpec.Sig.Make
import HipSpec.Sig.Get

import HipSpec.Params

import HipSpec.Id (tryGetGHCVar,tryGetGHCTyCon)

import qualified Data.Foldable as F

import CoreSyn (flattenBinds)
import CoreMonad (liftIO)
import DynFlags
import GHC
import GHC.Paths
import HscTypes
#if __GLASGOW_HASKELL__ < 708
import StaticFlags
#endif

import System.FilePath

import Var

import HipSpec.GHC.Unfoldings
import HipSpec.GHC.Dicts (inlineDicts)
import HipSpec.GHC.Utils
import HipSpec.Utils

import HipSpec.Sig.Scope

import qualified Data.Map as M

import Data.Maybe
import Data.List

import Control.Monad

import SimplCore
import CoreSyn

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | The result from calling GHC
data EntryResult = EntryResult
    { sig_infos :: [SigInfo]
    , prop_ids  :: [Var]
    , extra_tcs :: [TyCon]
    }

-- | Signature from QuickSpec
data SigInfo = SigInfo
    { sig          :: Signature
    , resolve_map  :: ResolveMap
    }

execute :: Params  -> IO EntryResult
execute params@Params{..} = do

    -- Use -threaded
#if __GLASGOW_HASKELL__ < 708
    addWay WayThreaded
    addWay WayDyn
#endif

    -- Notify where ghc is installed
    runGhc (Just libdir) $ do

        -- Set interpreted so we can get the signature,
        -- and expose all unfoldings
        dflags0 <- getSessionDynFlags
        let dflags =
#if __GLASGOW_HASKELL__ >= 708
                updateWays $
                addWay' WayThreaded $
                addWay' WayDyn $
#endif
                     dflags0 { ghcMode = CompManager
                             , optLevel = 1
                             , profAuto = NoProfAuto
                             , importPaths = include ++ includePaths dflags0 ++ ["."]
                             }
                        `wopt_unset` Opt_WarnOverlappingPatterns
#if __GLASGOW_HASKELL__ >= 708
                        `gopt_unset` Opt_IgnoreInterfacePragmas
                        `gopt_unset` Opt_OmitInterfacePragmas
                        `gopt_set` Opt_ExposeAllUnfoldings
                        `xopt_set` Opt_TypeOperators
#else
                        `dopt_unset` Opt_IgnoreInterfacePragmas
                        `dopt_unset` Opt_OmitInterfacePragmas
                        `dopt_set` Opt_ExposeAllUnfoldings
                        `dopt_set` Opt_TypeOperators
#endif
        _ <- setSessionDynFlags dflags

            -- add .hs if it is not present (apparently not supporting lhs)
        let file_with_ext = replaceExtension file ".hs"

        target <- guessTarget file_with_ext Nothing
        addTarget target
        r <- load LoadAllTargets
        when (failed r) $ error "Compilation failed!"

        mod_graph <- getModuleGraph
        let mod_sum = findModuleSum file_with_ext mod_graph

        -- Parse, typecheck and desugar the module
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t

        let modguts = dm_core_module d

        let binds = fixUnfoldings (inlineDicts (flattenBinds (mg_binds modguts)))

        let fix_id :: Id -> Id
            fix_id = fixId binds

        whenFlag params PrintCore (liftIO (putStrLn (showOutputable binds)))

        -- Set the context for evaluation
        setContext $
            [ IIDecl (simpleImportDecl (moduleName (ms_mod mod_sum)))
            , IIDecl (qualifiedImport "QuickSpec.Signature")
            , IIDecl (qualifiedImport "QuickSpec.Type")
            , IIDecl (qualifiedImport "QuickSpec.Term")
            , IIDecl (qualifiedImport "Data.Constraint")
            , IIDecl (qualifiedImport "Test.QuickCheck")
            , IIDecl (qualifiedImport "GHC.Types")
            , IIDecl (qualifiedImport "GHC.Base")
            , IIDecl (qualifiedImport "Prelude")
            ]
            -- Also include the imports the module is importing
            ++ map (IIDecl . unLoc) (ms_textual_imps mod_sum)

        -- Get ids in scope to find the properties (fix their unfoldings, too)
        ids_in_scope <- getIdsInScope fix_id

        let only' :: [String]
            only' = concatMap (splitOn ",") only

            props :: [Var]
            props =
                [ i
                | i <- ids_in_scope
                , varWithPropType i
                , not (varFromPrelude i)
                , null only || varToString i `elem` only'
                ]

        -- Make or get signature
        -- cond_id <- return Nothing -- findCondId params

        sigs <-
            if TranslateOnly `elem` debug_flags
            then return []
            else if auto
            then makeSignature params props
            else fmap maybeToList getSignature

        -- Make signature map
        --
        -- The extra_ids comes from --extra and --extra-trans fields from
        -- the auto signature generation
        (sig_infos,extra_ids,extra_tcs) <- fmap unzip3 . forM sigs $ \ sig0 -> do
            let sig = renumber sig0
            resolve_map@(ResolveMap m n) <- makeResolveMap params sig
            let (ids,tcs) = (map fst (M.elems m),M.elems n)
            return (SigInfo{..},ids,tcs)

        let toplvl_binds | tr_mod    = map (fix_id . fst) binds
                         | otherwise = []

        whenFlag params PrintCore (liftIO (putStrLn (showOutputable toplvl_binds)))

        -- Wrapping up
        return EntryResult
            { sig_infos = sig_infos
            , prop_ids  = props ++ map fix_id (mapMaybe tryGetGHCVar (concat extra_ids)) ++ toplvl_binds
            , extra_tcs = nubSorted (mapMaybe tryGetGHCTyCon (concatMap F.toList (concat extra_tcs)))
            }

{-
findCondId :: Params -> Ghc (Maybe Id)
findCondId Params{cond_name} = case cond_name of
    "" -> return Nothing
    cn -> do
        tyth <- lookupString cn
        case tyth of
            AnId i:_ -> return (Just i)
            _        -> error $ "Predicate " ++ cn ++ " is not an identifier!"
-}

findModuleSum :: FilePath -> [ModSummary] -> ModSummary
findModuleSum file
    = fromMaybe (error $ "Cannot find module " ++ file)
    . find (maybe False (== file) . summaryHsFile)

summaryHsFile :: ModSummary -> Maybe FilePath
summaryHsFile = ml_hs_file . ms_location

qualifiedImport :: String -> ImportDecl name
qualifiedImport = qualifiedImportDecl . mkModuleName

qualifiedImportDecl :: ModuleName -> ImportDecl name
qualifiedImportDecl m = (simpleImportDecl m) { ideclQualified = True }

