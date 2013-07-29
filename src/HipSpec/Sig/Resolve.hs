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

import DataCon
import GHC hiding (Sig)
import CoreMonad

import HipSpec.Params

import Data.Either
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Typeable as Typeable

import HipSpec.GHC.Utils


-- | Mappings for QuickSpec symbols and Typeable Tycons to GHC Core structures
data ResolveMap = ResolveMap
    { sym_map   :: Map Symbol Id
    , tycon_map :: Map Typeable.TyCon TyCon
    }


maybeLookupSym :: ResolveMap -> Symbol -> Maybe Id
maybeLookupSym sm s = M.lookup s (sym_map sm)

maybeLookupTyCon :: ResolveMap -> Typeable.TyCon -> Maybe TyCon
maybeLookupTyCon sm t = M.lookup t (tycon_map sm)

debugStr :: String
debugStr =
    "\nDebug the conversions between QuickSpec signatures and GHC Core " ++
    "structures with --debug-scope and debug-str-conv."

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

makeResolveMap :: Params -> Sig -> Map Name TyThing -> Ghc ResolveMap
makeResolveMap p@Params{..} sig named_things = do

    sig_names :: Map Symbol [Name] <- M.fromList `fmap`
        mapM (\ symb -> fmap ((,) symb) (parseName (name symb)))
             (constantSymbols sig)
    sig_tycons :: Map Typeable.TyCon [Name] <- M.fromList `fmap`
        mapM (\ tc -> fmap ((,) tc) (parseName (Typeable.tyConName tc)))
             (concatMap (typeRepTyCons . symbolType) (symbols sig))

    let symb_tr :: Map Symbol [TyThing]
        symb_tr = trans named_things sig_names

        tyc_tr :: Map Typeable.TyCon [TyThing]
        tyc_tr = trans named_things sig_tycons


    whenFlag p DebugScope $ liftIO $ do
        putStrLn "Names in scope"
        mapM_ putStrLn
            [ " " ++ showOutputable n ++ " :: " ++ showOutputable t
            | (n,t) <- M.toList named_things
            ]
        putStrLn "Functions and constructors"
        mapM_ putStrLn
            [ " " ++ name n ++ " -> " ++ showOutputable ns
            | (n,ns) <- M.toList sig_names
            ]
        putStrLn "Type constructors"
        mapM_ putStrLn
            [ " " ++ show tc ++ " -> " ++ showOutputable ns
            | (tc,ns) <- M.toList sig_tycons
            ]
        putStrLn "Symbol translation"
        mapM_ putStrLn
            [ " " ++ show s ++ " -> " ++ showOutputable ts
            | (s,ts) <- M.toList symb_tr
            ]
        putStrLn "Type constructor translation"
        mapM_ putStrLn
            [ " " ++ show tc ++ " -> " ++ showOutputable ts
            | (tc,ts) <- M.toList tyc_tr
            ]

    let justOr :: (a -> Maybe b) -> (c -> [a] -> e) -> c -> [a] -> Either e b
        justOr k h a xs = maybe (Left (h a xs)) Right (listToMaybe $ mapMaybe k xs)

        err s a ts = show a ++ " should be a " ++ s ++ ", but is bound to "
                            ++ showOutputable ts
                            ++ ", fix your signature!"

        symb_sn :: Either [String] (Map Symbol Id)
        symb_sn = sanity (k `justOr` err "function or constructor") symb_tr
          where
            k (AnId i)     = Just i
            k (ADataCon i) = Just (dataConWorkId i)
            k _            = Nothing

        tyc_sn :: Either [String] (Map Typeable.TyCon TyCon)
        tyc_sn = sanity (k `justOr` err "type constructor") tyc_tr
          where
            k (ATyCon ty_con) = Just ty_con
            k _               = Nothing

    liftIO $ do
        print_errs symb_sn
        print_errs tyc_sn

    case (symb_sn,tyc_sn) of
        (Right symb,Right tyc) -> do
            whenFlag p DebugStrConv $ liftIO $ do
                putStrLn "Functions and constructors"
                let show_sym s = show s ++ "(" ++ show (index s) ++ ")"
                mapM_ putStrLn
                    [ show_sym s ++ " -> " ++ showOutputable i
                    | (s,i) <- M.toList symb
                    ]
                putStrLn "Type constructors"
                mapM_ putStrLn
                    [ show tc ++ " -> " ++ showOutputable tc'
                    | (tc,tc') <- M.toList tyc
                    ]
            return ResolveMap
                { sym_map   = symb
                , tycon_map = tyc
                }
        _ -> error "Couldn't understand the strings in your signature!"

trans :: Ord b => Map b c -> Map a [b] -> Map a [c]
trans m = fmap (\ bs -> catMaybes [ M.lookup b m | b <- bs ])

sanity :: Ord a =>
          (a -> t -> Either e t')
       -- ^ Function to sanitize with
       -> Map a t
       -- ^ The map that is not sanity checked
       -> Either [e] (Map a t')
       -- ^ Either a list of errors or a sane map
sanity k m = case partitionEithers lst of
    ([],xs)  -> Right (M.fromList xs)
    (errs,_) -> Left errs
  where
    lst = [ case k a t of
                Right t' -> Right (a,t')
                Left e   -> Left e
          | (a,t) <- M.toList m ]

print_errs :: Either [String] a -> IO ()
print_errs (Left errs) = mapM_ putStrLn errs
print_errs _           = return ()

