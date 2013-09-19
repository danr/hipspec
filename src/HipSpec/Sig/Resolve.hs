{-# LANGUAGE RecordWildCards,ViewPatterns,ScopedTypeVariables #-}
{-

    Find appropriate translations of QuickSpec strings to core
    bindings, data constructors or type constructors.

-}
module HipSpec.Sig.Resolve
    ( ResolveMap(..)
    , lookupSym
    , lookupTyCon
    , maybeLookupSym
    , maybeLookupTyCon
    , makeResolveMap
    , debugStr
    ) where

import Test.QuickSpec.Signature
import Test.QuickSpec.Term hiding (Var,symbols,size)
import Test.QuickSpec.Utils.Typed (typeRepTyCons)

import GHC hiding (Sig)
import CoreMonad

import HipSpec.Params

import Control.Monad

import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Typeable as Typeable

import HipSpec.GHC.Utils
import HipSpec.Sig.Scope
import HipSpec.Utils

-- | Mappings for QuickSpec symbols and Typeable Tycons to GHC Core structures
data ResolveMap = ResolveMap
    { sym_map   :: Map Symbol Id
    , tycon_map :: Map Typeable.TyCon TyCon
    }


makeResolveMap :: Params -> Sig -> Ghc ResolveMap
makeResolveMap p@Params{..} sig = do

    -- functions and constrctors
    syms <- forM (nubSorted (constantSymbols sig)) $ \ symb -> do
        things <- lookupString (name symb)
        case mapJust thingToId things of
            Just i  -> return (symb,i)
            Nothing -> error $ "Not in scope: " ++ name symb

    -- type constructors
    tcs <- forM (nubSorted (concatMap (typeRepTyCons . symbolType) (symbols sig))) $ \ tc -> do
        things <- lookupString (Typeable.tyConName tc)
        let getTc (ATyCon tc') = Just tc'
            getTc _            = Nothing
        case mapJust getTc things of
            Just tc' -> return (tc,tc')
            Nothing  -> error $ "Type constructor not in scope:" ++ Typeable.tyConName tc

    whenFlag p DebugStrConv $ liftIO $ do
        putStrLn "Symbol translation"
        mapM_ putStrLn
            [ " " ++ show s ++ " -> " ++ showOutputable ts
            | (s,ts) <- syms
            ]
        putStrLn "Type constructor translation"
        mapM_ putStrLn
            [ " " ++ show tc ++ " -> " ++ showOutputable ts
            | (tc,ts) <- tcs
            ]

    return ResolveMap
        { sym_map   = M.fromList syms
        , tycon_map = M.fromList tcs
        }

maybeLookupSym :: ResolveMap -> Symbol -> Maybe Id
maybeLookupSym sm s = M.lookup s (sym_map sm)

maybeLookupTyCon :: ResolveMap -> Typeable.TyCon -> Maybe TyCon
maybeLookupTyCon sm t = M.lookup t (tycon_map sm)

debugStr :: String
debugStr =
    "\nDebug the conversions between QuickSpec signatures and GHC Core " ++
    "structures with --debug-str-conv."

lookupSym :: ResolveMap -> Symbol -> Id
lookupSym m s = fromMaybe (error err_str) (maybeLookupSym m s)
  where
    err_str =
        "Cannot translate QuickSpec's " ++ show s ++
        " to Core representation! " ++ debugStr

lookupTyCon :: ResolveMap -> Typeable.TyCon -> TyCon
lookupTyCon m s = fromMaybe (error err_str) (maybeLookupTyCon m s)
  where
    err_str =
        "Cannot translate Data.Typeable type constructor " ++ show s ++
        " to Core representation! " ++ debugStr
