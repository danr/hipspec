-- | Gets the GHC Core information we need, also sets up the system for later
--   QuickSpec execution
{-# LANGUAGE RecordWildCards #-}
module HipSpec.Read where

import HipSpec.ParseDSL

-- import Data.List.Split (splitOn)

{-
import HipSpec.GHC.Types
import HipSpec.GHC.SigMap
import HipSpec.GHC.MakeSig
import HipSpec.GHC.GetSig
import HipSpec.Params
-}

-- import CoreMonad
import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
import StaticFlags

import Var

import Lang.Unfoldings
-- import Lang.Utils

-- import HipSpec.GHC.Delude
-- import Halo.Shared
-- import Halo.Unfoldings

import qualified Data.Map as M
import Data.Map (Map)

import Data.Maybe
import Data.List

import Control.Monad

execute :: FilePath -> IO [Var]
execute file = do

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

{-
        when dump_core $ liftIO $ do
            putStrLn "== INIT CORE =="
            putStrLn $ showOutputable binds
            -}

        -- Set the context for evaluation
        setContext $
            [ IIDecl (simpleImportDecl (moduleName (ms_mod mod_sum)))
            , IIDecl (qualifiedImportDecl (mkModuleName "Test.QuickSpec.Signature"))
            , IIDecl (qualifiedImportDecl (mkModuleName "Test.QuickSpec.Prelude"))
            , IIDecl (qualifiedImportDecl (mkModuleName "GHC.Types"))
            , IIDecl (qualifiedImportDecl (mkModuleName "Prelude"))
            ]
            -- Also include the imports the module is importing
            ++ map (IIDecl . unLoc) (ms_textual_imps mod_sum)

        -- Get everything in scope
        named_things <- getNamedThings fix_id

        let {- only' :: [String]
            only' = concatMap (splitOn ",") only
            -}

            props :: [Var]
            props =
                [ i
                | (_,AnId i) <- M.toList named_things
                , varWithPropType i
--                , null only' || varString i `elem` only'
                ]

        {-
        -- Make or get signature
        m_sig <- if auto
            then makeSignature params named_things props
            else getSignature (map fst $ M.toList named_things)

        -- Make signature map
        sig_info <- case m_sig of
            Nothing -> return Nothing
            Just sig -> do
                sig_map <- makeSigMap params sig named_things
                return $ Just SigInfo
                    { sig     = sig
                    , sig_map = sig_map
                    }
        -}

        -- Wrapping up
        return props

        {- EntryResult
            { prop_ids = props
--            , sig_info = sig_info
            }
            -}

qualifiedImportDecl :: ModuleName -> ImportDecl name
qualifiedImportDecl m = (simpleImportDecl m) { ideclQualified = True }

-- | Getting the names in scope
--
--   Context for evaluation needs to be set before
getNamedThings :: (Id -> Id) -> Ghc (Map Name TyThing)
getNamedThings fix_id = do

    -- Looks up a name and tries to associate it with a typed thing
    let lookup_name :: Name -> Ghc (Maybe (Name,TyThing))
        lookup_name n = fmap (fmap (\ (tyth,_,_) -> (n,tyth))) (getInfo n)

    -- Get the types of all names in scope
    ns <- getNamesInScope
    maybe_named_things <- mapM lookup_name ns

    return $ M.fromList
        [ (n,mapTyThingId fix_id tyth)
        | Just (n,tyth) <- maybe_named_things
        ]

mapTyThingId :: (Id -> Id) -> TyThing -> TyThing
mapTyThingId k (AnId i) = AnId (k i)
mapTyThingId _ tyth     = tyth

