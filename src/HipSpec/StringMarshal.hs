{-# LANGUAGE RecordWildCards,ViewPatterns #-}
{-

    Find appropriate translations of QuickSpec strings to core
    bindings, data constructors or type constructors.

-}
module HipSpec.StringMarshal
    ( StrMarsh
    , maybeLookupSym
    , maybeLookupTyCon
    , makeStringMarshallings
    ) where


import Test.QuickSpec.Term

import DataCon
import GHC

import Halo.Shared
import HipSpec.Execute
import HipSpec.Params

import Control.Monad
import Data.Either
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Typeable as Typeable

type StrMarsh = (Map Symbol Id,Map Typeable.TyCon TyCon)

maybeLookupSym :: StrMarsh -> Symbol -> Maybe Id
maybeLookupSym (m,_) s = M.lookup s m

maybeLookupTyCon :: StrMarsh -> Typeable.TyCon -> Maybe TyCon
maybeLookupTyCon (_,m) t = M.lookup t m

makeStringMarshallings :: Params -> ExecuteResult -> IO StrMarsh
makeStringMarshallings Params{..} ExecuteResult{..} = do

    when db_names $ do
        putStrLn "Names in scope"
        mapM_ putStrLn
            [ showOutputable n ++ " :: " ++ showOutputable t
            | (n,t) <- M.toList named_things
            ]
        putStrLn "Functions and constructors"
        mapM_ putStrLn
            [ name n ++ " -> " ++ showOutputable ns
            | (n,ns) <- M.toList signature_names
            ]
        putStrLn "Type constructors"
        mapM_ putStrLn
            [ show tc ++ " -> " ++ showOutputable ns
            | (tc,ns) <- M.toList signature_tycons
            ]

    print_errs symb_sn
    print_errs tyc_sn

    case (symb_sn,tyc_sn) of
        (Right symb,Right tyc) -> do
            when db_str_marsh $ do
                putStrLn "Functions and constructors"
                mapM_ putStrLn
                    [ show s ++ " -> " ++ showOutputable i
                    | (s,i) <- M.toList symb
                    ]
                putStrLn "Type constructors"
                mapM_ putStrLn
                    [ show tc ++ " -> " ++ showOutputable tc'
                    | (tc,tc') <- M.toList tyc
                    ]
            return (symb,tyc)
        _ -> error "Couldn't understand the strings in your signature!"

  where

    symb_tr :: Map Symbol [TyThing]
    symb_tr = trans named_things signature_names

    tyc_tr :: Map Typeable.TyCon [TyThing]
    tyc_tr = trans named_things signature_tycons

    justOr :: (a -> Maybe b) -> (c -> [a] -> e) -> c -> [a] -> Either e b
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





