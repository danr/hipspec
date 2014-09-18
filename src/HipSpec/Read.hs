-- | Gets the GHC Core information we need, also obtains or creates the
--   QuickSpec signature
{-# LANGUAGE RecordWildCards, NamedFieldPuns, CPP #-}
module HipSpec.Read (execute,EntryResult(..),SigInfo(..)) where

import Test.QuickSpec.Signature (Sig)

import HipSpec.ParseDSL

import Data.List.Split (splitOn)

import HipSpec.Sig.Resolve
import HipSpec.Sig.Make
import HipSpec.Sig.Get
import HipSpec.Sig.Symbols

import HipSpec.Params

import qualified HipSpec.Id as HS
import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Pretty as HS

import CoreSyn (flattenBinds)
import CoreMonad (liftIO)
import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
#if __GLASGOW_HASKELL__ < 708
import StaticFlags
#endif

import System.FilePath

import Var

import HipSpec.GHC.Unfoldings
import HipSpec.GHC.Utils

import HipSpec.Sig.Scope

import qualified Data.Map as M

import Data.Maybe
import Data.List

import Control.Monad


{-# ANN module "HLint: ignore Use camelCase" #-}

-- | The result from calling GHC
data EntryResult = EntryResult
    { sig_infos :: [SigInfo]
    , prop_ids  :: [Var]
    , extra_tcs :: [TyCon]
    , extra_unf :: [S.Function HS.Id]
    }

-- | Signature from QuickSpec
data SigInfo = SigInfo
    { sig          :: Sig
    , resolve_map  :: ResolveMap
    , symbol_map   :: SymbolMap
    , cond_id      :: Maybe Id
    , cond_mono_ty :: Maybe Type
    }

{-
addPluginModuleName :: String -> DynFlags -> DynFlags
addPluginModuleName name d = d { pluginModNames = (mkModuleName name) : (pluginModNames d) }

exposePackageId :: String -> DynFlags -> DynFlags
exposePackageId p d = d { packageFlags = ExposePackage p : packageFlags d }
-}

execute :: Params -> [S.Function HS.Id] -> IO EntryResult
execute params@Params{..} extra_defs = do

    -- Use -threaded
#if __GLASGOW_HASKELL__ < 708
    addWay WayThreaded
#endif

    -- Notify where ghc is installed
    runGhc (Just libdir) $ do

        -- Set interpreted so we can get the signature,
        -- and expose all unfoldings
        dflags0 <- getSessionDynFlags
        let dflags =
--                exposePackageId "hipspec" $
--                addPluginModuleName "HipSpec.UnfoldPlugin" $
#if __GLASGOW_HASKELL__ >= 708
                addWay' WayThreaded
#endif
                    (dflags0 { ghcMode = CompManager
                             , optLevel = 1
                             , profAuto = NoProfAuto
                             }
                        `wopt_unset` Opt_WarnOverlappingPatterns
                        `xopt_set` Opt_ExplicitForAll
#if __GLASGOW_HASKELL__ >= 708
--                        `dopt_set` Opt_D_dump_simpl_stats
--                        `dopt_set` Opt_D_dump_simpl
--                        `dopt_set` Opt_D_verbose_core2core
                        `gopt_unset` Opt_IgnoreInterfacePragmas
                        `gopt_unset` Opt_OmitInterfacePragmas
                        `gopt_set` Opt_ExposeAllUnfoldings)
#else
                        `dopt_unset` Opt_IgnoreInterfacePragmas
                        `dopt_unset` Opt_OmitInterfacePragmas
                        `dopt_set` Opt_ExposeAllUnfoldings)
#endif
        _ <- setSessionDynFlags dflags

--        _ <- setInteractiveDynFlags dflags

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

            binds = fixUnfoldings (mg_binds modguts)

            fix_id :: Id -> Id
            fix_id = fixId binds

        whenFlag params PrintCore (liftIO (putStrLn (showOutputable binds)))

        -- Set the context for evaluation
        setContext $
            [ IIDecl (simpleImportDecl (moduleName (ms_mod mod_sum)))
            , IIDecl (qualifiedImport "Test.QuickSpec.Signature")
            , IIDecl (qualifiedImport "Test.QuickSpec.Prelude")
            , IIDecl (qualifiedImport "Test.QuickCheck")
            , IIDecl (qualifiedImport "GHC.Types")
            , IIDecl (qualifiedImport "Prelude")
            ]
            -- Also include the imports the module is importing
            ++ map (IIDecl . unLoc) (ms_textual_imps mod_sum)

        idflgs <- getInteractiveDynFlags

        liftIO $ print (gopt Opt_ExposeAllUnfoldings idflgs)

        synth_fns' <- forM extra_defs $ \ def -> do
          let s = "let\n" ++ unlines (map ("    " ++) (lines (HS.showLikeHaskell def)))
          liftIO $ putStrLn "Adding:"
          liftIO $ putStrLn s
          rr <- runStmtWithLocation "hipspec_synthesis" 0 s RunToCompletion
          case rr of
            RunOk [nm] -> do
              liftIO $ putStrLn $ "got name: " ++ show nm
              th <- lookupName nm
              case thingToId =<< th of
                Just i -> do
                  liftIO $ putStrLn "one id, perfect"
                  liftIO $ putStrLn $ showOutputable $ maybeUnfolding i
                  return [(i,S.renameFunction def (HS.idFromName nm))]
                Nothing -> do
                  liftIO $ putStrLn "not an id"
                  return []
            RunOk nms -> do
              liftIO $ putStrLn $ "got many names: " ++ show nms
              return []
            RunException _e -> do
              liftIO $ putStrLn "exception"
              return []
            RunBreak{} -> do
              liftIO $ putStrLn "break"
              return []

        let synth_fns = concat synth_fns'
            synth_ids = map fst synth_fns

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
        cond_id <- findCondId params

        (sigs,cond_mono_ty) <- if auto
            then (makeSignature params synth_ids cond_id props)
            else fmap (flip (,) Nothing . maybeToList) getSignature


        -- Make signature map
        --
        -- The extra_ids comes from --extra and --extra-trans fields from
        -- the auto signature generation
        (sig_infos,extra_ids,extra_tcs) <- fmap unzip3 . forM sigs $ \ sig -> do
            resolve_map <- makeResolveMap params sig
            let symbol_map = makeSymbolMap resolve_map sig
                (ids,tcs) = case resolve_map of
                    ResolveMap m n -> (M.elems m,M.elems n)

            whenFlag params DebugStrConv (liftIO (putStrLn (show symbol_map)))

            return (SigInfo{..},ids,tcs)

        let toplvl_binds | tr_mod    = map (fix_id . fst) (flattenBinds binds)
                         | otherwise = []

        whenFlag params PrintCore (liftIO (putStrLn (showOutputable toplvl_binds)))

        -- Wrapping up
        return EntryResult
            { sig_infos = sig_infos
            , prop_ids  = props ++ concat extra_ids ++ toplvl_binds ++ maybeToList cond_id
            , extra_tcs = concat extra_tcs
            , extra_unf = map snd synth_fns
            }

findCondId :: Params -> Ghc (Maybe Id)
findCondId Params{cond_name} = case cond_name of
    "" -> return Nothing
    cn -> do
        tyth <- lookupString cn
        case tyth of
            AnId i:_ -> return (Just i)
            _        -> error $ "Predicate " ++ cn ++ " is not an identifier!"


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

