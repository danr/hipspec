{-# LANGUAGE RecordWildCards,ViewPatterns,ScopedTypeVariables #-}
{-

    Find appropriate translations of QuickSpec strings to core
    bindings, data constructors or type constructors.

-}
module HipSpec.Sig.Resolve
    ( ResolveMap(..)
    , lookupCon
    , lookupTyCon
    , maybeLookupCon
    , maybeLookupTyCon
    , makeResolveMap
    , debugStr
    ) where

import QuickSpec.Signature
import QuickSpec.Type
import QuickSpec.Term hiding (Var,symbols,size)
import Data.Rewriting.Term (funs)

import GHC
import CoreMonad
import qualified Id as GHC

import HipSpec.Params

import Control.Monad

import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Typeable as Typeable

import HipSpec.GHC.Utils
import HipSpec.Sig.Scope
import HipSpec.Utils
import HipSpec.Id as HS
import HipSpec.Lang.Type
import HipSpec.Lang.CoreToRich
import qualified HipSpec.Lang.Rich as R

-- | Mappings for QuickSpec symbols and Typeable Tycons to GHC and HipSpec structures
data ResolveMap = ResolveMap
    { con_map   :: Map Constant (GHC.Id,PolyType HS.Id)
    , tycon_map :: Map Typeable.TyCon GHC.TyCon
    }

makeResolveMap :: Params -> Signature -> Ghc ResolveMap
makeResolveMap p@Params{..} sig = do

    -- constants (functions, constructors)
    syms <- forM (constants sig) $ \ x -> do
        things <- lookupString (conName x)
        case mapJust thingToId things of
            Just v  -> case runTM (trVar v) of
                Right (R.Gbl _hs_id hs_polytype []) ->
                    -- assert (_hs_id == idFromVar i)
                    return (x,(v,hs_polytype))
                _ -> error $ "Not a global variable: " ++ show x
            Nothing -> error $ "Not in scope: " ++ show x

    -- type constructors
    tcs <- forM (nubSorted (concatMap (funs . typ) (constants sig))) $ \ tc0 -> do
        let tc = toTyCon tc0
        things <- lookupString (Typeable.tyConName tc)
        let getTc (ATyCon tc') = Just tc'
            getTc _            = Nothing
        case mapJust getTc things of
            Just ghc_tc -> return (tc,ghc_tc)
            Nothing     -> error $ "Type constructor not in scope:" ++ Typeable.tyConName tc

    whenFlag p DebugStrConv $ liftIO $ do
        putStrLn "Constant translation"
        mapM_ putStrLn
            [ " " ++ show s ++ " -> " ++ showOutputable i ++ "," ++ show pt
            | (s,(i,pt)) <- syms
            ]
        putStrLn "Type constructor translation"
        mapM_ putStrLn
            [ " " ++ show tc ++ " -> " ++ showOutputable ts
            | (tc,ts) <- tcs
            ]

    return ResolveMap
        { con_map   = M.fromList syms
        , tycon_map = M.fromList tcs
        }

maybeLookupCon :: ResolveMap -> Constant -> Maybe (GHC.Id,PolyType HS.Id)
maybeLookupCon sm s = M.lookup s (con_map sm)

maybeLookupTyCon :: ResolveMap -> Typeable.TyCon -> Maybe GHC.TyCon
maybeLookupTyCon sm t = M.lookup t (tycon_map sm)

debugStr :: String
debugStr =
    "\nDebug the conversions between QuickSpec signatures and GHC Core " ++
    "structures with --debug-str-conv."

lookupCon :: ResolveMap -> Constant -> (GHC.Id,PolyType HS.Id)
lookupCon m s = fromMaybe (error err_str) (maybeLookupCon m s)
  where
    err_str =
        "Cannot translate QuickSpec's " ++ show s ++
        " to Core representation! " ++ debugStr

lookupTyCon :: ResolveMap -> Typeable.TyCon -> GHC.TyCon
lookupTyCon m s = fromMaybe (error err_str) (maybeLookupTyCon m s)
  where
    err_str =
        "Cannot translate Data.Typeable type constructor " ++ show s ++
        " to Core representation! " ++ debugStr
