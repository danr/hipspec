{-# LANGUAGE ScopedTypeVariables #-}
module HipSpec.Execute where

import Test.QuickSpec.Signature
import Test.QuickSpec.Term hiding (Var,symbols)
import Test.QuickSpec.Utils.Typed (typeRepTyCons)

import CoreMonad
import DynFlags
import GHC hiding (Sig)
import GHC.Paths
import HscTypes
-- import SimplCore
import StaticFlags
import OccName
import Name
import CoreSyn

import HipSpec.Trans.SrcRep
import Halo.Shared
import Halo.Unfoldings

import qualified Data.Typeable as Typeable

import Data.Map (Map)
import qualified Data.Map as M

import Data.Dynamic

import Data.Maybe
import Data.List

import Control.Monad

import HipSpec.Heuristics.Calls

data ExecuteResult = ExecuteResult
    { signature_sig    :: Maybe Sig
    , signature_names  :: Map Symbol [Name]
    , signature_tycons :: Map Typeable.TyCon [Name]
    , named_things     :: Map Name TyThing
    , init_core_binds  :: [CoreBind]
    , dyn_flags        :: DynFlags
    }

execute :: FilePath -> IO ExecuteResult
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
        target <- guessTarget (file ++ ".hs") Nothing
        _ <- addTarget target
        r <- load LoadAllTargets
        when (failed r) $ error "Compilation failed!"

        mod_graph <- getModuleGraph
        let mod_sum = fromMaybe (error $ "Cannot find module " ++ file)
                    $ find (\m -> ms_mod_name m == mkModuleName file
                               || ms_mod_name m == mkModuleName (replace '/' '.' file)
                               || ms_mod_name m == mkModuleName "Main"
                               || ml_hs_file (ms_location m) == Just file)
                           mod_graph
              where replace a b xs = map (\ x -> if x == a then b else x) xs

        -- Set the context for later evaluation
        setContext
            $  [IIDecl (simpleImportDecl (moduleName (ms_mod mod_sum)))]
            -- Also include the imports the module is importing
            -- (I know, crazy!)
            ++ map (IIDecl . unLoc) (ms_textual_imps mod_sum)

        -- Parse, typecheck and desugar the module
        p <- parseModule mod_sum
        t <- typecheckModule p
        d <- desugarModule t

        -- Get the session so we can use tcRnLookupName and core2core optimise
        -- hsc_env <- getSession

        let modguts = dm_core_module d

        -- Get the modguts (and optimise it)
--        modguts <- liftIO (core2core hsc_env (dm_core_module d))

        -- Now we can load the module (so we can later evaluate in it)
        -- _ <- load LoadAllTargets loadModule d
        -- (doesn't seem to be necessary?)

        -- Looks up a name and tries to associate it with a typed thing
        let lookup_name :: Name -> Ghc (Maybe (Name,TyThing))
            lookup_name n = fmap (fmap (\ (tyth,_,_) -> (n,tyth))) (getInfo n)

        -- Get the types of all names in scope
        ns <- getNamesInScope
        maybe_named_things <- mapM lookup_name ns

        -- Try to get a quickSpec signature
        m_sig <- getSignature ns

        -- For each symbols from the signature, find the associated Names in
        -- scope (should be exactly one, but we'll check this later)
        sig_names <- case m_sig of
            Nothing  -> return []
            Just sig -> mapM (\ symb -> fmap ((,) symb) (parseName (name symb)))
                             (constantSymbols sig)

        sig_tycons <- case m_sig of
            Nothing  -> return []
            Just sig -> mapM (\ tc -> fmap ((,) tc) (parseName (Typeable.tyConName tc)))
                             (concatMap (typeRepTyCons . symbolType) (symbols sig))

        let binds = fixUnfoldings (mg_binds modguts)

        let isPropBinder (x,_) = isPropType x

            core_props = filter isPropBinder $ flattenBinds binds

            interesting_ids :: [Id]
            interesting_ids
                = varSetElems
                $ unionVarSets (map (transFrom M.empty . exprCalls . snd) core_props)

        liftIO $ putStrLn (showOutputable interesting_ids)

        -- Wrapping up
        return ExecuteResult
            { signature_sig    = m_sig
            , signature_names  = M.fromList sig_names
            , signature_tycons = M.fromList sig_tycons
            , named_things     = M.fromList (catMaybes maybe_named_things)
            , init_core_binds  = binds
            , dyn_flags        = dflags
            }

-- | Getting the signature.
getSignature :: [Name] -> Ghc (Maybe Sig)
getSignature scope
    | any (\ n -> occNameString (nameOccName n) == "sig") scope
        = liftM2 mplus (fromDynamic `fmap` dynCompileExpr "sig")
                       (fromDynamic `fmap` dynCompileExpr "signature sig")
    | otherwise = return Nothing

