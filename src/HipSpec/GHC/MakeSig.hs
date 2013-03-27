{-# LANGUAGE RecordWildCards #-}
module HipSpec.GHC.MakeSig (makeSignature) where

import Data.List.Split (splitOn)

import CoreMonad
import DataCon
import GHC hiding (Sig)
import Type
import Var

import Data.Dynamic
import Data.List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M

import Halo.Shared

import HipSpec.GHC.Delude
import HipSpec.Heuristics.Calls
import HipSpec.Params

import Test.QuickSpec.Signature

import Control.Monad

makeSignature :: Params -> Map Name TyThing -> [Var] -> Ghc (Maybe Sig)
makeSignature Params{..} named_things prop_ids = do

    liftIO $ do
        when dump_auto_sig $ putStrLn (expr_str "\n\t,")
        when dump_auto_info $ do
            putStrLn $ "--extra=" ++ show extra' ++ ":" ++ showOutputable extra_ids
            putStrLn $ "--extra-trans=" ++ show extra_trans' ++ ":" ++ showOutputable extra_trans_ids
            putStrLn $ "Prop ids: " ++ show prop_ids ++ " (only=" ++ show only ++ ")"
            putStrLn $ "Transitive ids: " ++ showOutputable interesting_ids
            putStrLn $ "Final ids: " ++ showOutputable ids

    if null entries
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (expr_str ",")
  where
    extra' = concatMap (splitOn ",") extra
    extra_trans' = concatMap (splitOn ",") extra_trans

    named_things' :: Map String Id
    named_things' = M.fromList . mapMaybe (uncurry t) . M.toList $ named_things
      where
        t :: Name -> TyThing -> Maybe (String,Id)
        t n (AnId i)      = Just (nameString n,i)
        t n (ADataCon dc) = Just (nameString n,dataConWorkId dc)
        t _ _             = Nothing

    extra_trans_ids :: [Id]
    extra_trans_ids = mapMaybe (`M.lookup` named_things') extra_trans'

    interesting_ids :: VarSet
    interesting_ids = unionVarSets $
        map (transCalls M.empty) (prop_ids ++ extra_trans_ids)

    extra_ids :: [Id]
    extra_ids = mapMaybe (`M.lookup` named_things') extra'

    ids :: [Id]
    ids = varSetElems $ filterVarSet (\ x -> not (fromPrelude x || isPropType x)) $
            interesting_ids `unionVarSet` mkVarSet extra_ids

    expr_str x = "signature [" ++ intercalate x entries ++ "]"

    entries =
        [ unwords
            [ "Test.QuickSpec.Signature.fun" ++ show (varArity i)
            , show (varString i)
            , "(" ++ showOutputable i ++ ")"
            ]
        | i <- ids
        ] ++
        [ unwords
            [ "vars"
            , show ["x","y","z"]
            , "(Prelude.undefined :: " ++ showOutputable t ++ ")"
            ]
        | t <- types
        ]

    types = nubBy eqType $ concat
        [ ty : tys
        | i <- ids
        , let (tys,ty) = splitFunTys (varType i)
        ]

varArity :: Var -> Int
varArity = length . fst . splitFunTys . varType

