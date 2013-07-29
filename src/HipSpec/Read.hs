-- | Gets the GHC Core information we need, also obtains or creates the
--   QuickSpec signature
{-# LANGUAGE RecordWildCards #-}
module HipSpec.Read (execute,EntryResult(..),SigInfo(..)) where

import Test.QuickSpec.Signature (Sig)

import HipSpec.ParseDSL

import Data.List.Split (splitOn)

import HipSpec.Sig.Resolve
import HipSpec.Sig.Make
import HipSpec.Sig.Get
import HipSpec.Sig.Symbols

import HipSpec.Params

import CoreMonad (liftIO)
import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
import StaticFlags

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
    { sig_info  :: Maybe SigInfo
    , prop_ids  :: [Var]
    , extra_tcs :: [TyCon]
    }

-- | Signature from QuickSpec
data SigInfo = SigInfo
    { sig         :: Sig
    , resolve_map :: ResolveMap
    , symbol_map  :: SymbolMap
    }

execute :: Params  -> IO EntryResult
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
        let mod_sum = getModuleSum mod_graph file'

        -- Parse, typecheck and desugar the module
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t

        let modguts = dm_core_module d

            binds = fixUnfoldings (mg_binds modguts)

            fix_id :: Id -> Id
            fix_id = fixId binds

        -- Set the context for evaluation
        setContext $
            [ IIDecl (simpleImportDecl (moduleName (ms_mod mod_sum)))
            , IIDecl (qualifiedImport "Test.QuickSpec.Signature")
            , IIDecl (qualifiedImport "Test.QuickSpec.Prelude")
            , IIDecl (qualifiedImport "GHC.Types")
            , IIDecl (qualifiedImport "Prelude")
            ]
            -- Also include the imports the module is importing
            ++ map (IIDecl . unLoc) (ms_textual_imps mod_sum)

        -- Get everything in scope
        named_things <- getNamedThings fix_id

        let only' :: [String]
            only' = concatMap (splitOn ",") only

            props :: [Var]
            props =
                [ i
                | (_,AnId i) <- M.toList named_things
                , varWithPropType i
                , null only' || varToString i `elem` only'
                ]

        -- Make or get signature
        m_sig <- if auto
            then makeSignature params named_things props
            else getSignature (map fst $ M.toList named_things)

        -- Make signature map
        (sig_info,extra_ids,extra_tcs) <- case m_sig of
            Nothing -> return (Nothing,[],[])
            Just sig -> do
                resolve_map <- makeResolveMap params sig named_things
                let symbol_map = makeSymbolMap resolve_map sig
                    (ids,tcs) = case resolve_map of
                        ResolveMap m n -> (M.elems m,M.elems n)

                whenFlag params DebugStrConv (liftIO (putStrLn (show symbol_map)))

                return (Just SigInfo{..},ids,tcs)


        -- Wrapping up
        return EntryResult
            { sig_info  = sig_info
            , prop_ids  = props ++ extra_ids
            , extra_tcs = extra_tcs
            }

getModuleSum :: [ModSummary] -> [Char] -> ModSummary
getModuleSum mod_graph file
    = fromMaybe (error $ "Cannot find module " ++ file)
    $ find (\m -> ms_mod_name m == mkModuleName file
               || ms_mod_name m == mkModuleName (replace '/' '.' file)
               || ms_mod_name m == mkModuleName "Main"
               || ml_hs_file (ms_location m) == Just file)
           mod_graph
  where replace a b = map (\ x -> if x == a then b else x)

qualifiedImport :: String -> ImportDecl name
qualifiedImport = qualifiedImportDecl . mkModuleName

qualifiedImportDecl :: ModuleName -> ImportDecl name
qualifiedImportDecl m = (simpleImportDecl m) { ideclQualified = True }

