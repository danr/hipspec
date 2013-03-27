{-# LANGUAGE RecordWildCards #-}
module HipSpec.GHC.MakeSig (makeSignature) where

import HipSpec.Params
import HipSpec.Heuristics.Calls

import Test.QuickSpec.Signature

import CoreMonad
import GHC hiding (Sig)

import Var
import Type

import HipSpec.GHC.Delude
import Halo.Shared

import qualified Data.Map as M

import Data.Dynamic

import Data.List

makeSignature :: Params -> [Var] -> Ghc (Maybe Sig)
makeSignature Params{..} prop_ids = do
    liftIO $ putStrLn (showOutputable prop_ids)
    liftIO $ putStrLn (showOutputable interesting_ids)
    liftIO $ putStrLn (showOutputable ids)
    liftIO $ putStrLn expr_str
    liftIO $ print only

    fromDynamic `fmap` dynCompileExpr expr_str
  where
    interesting_ids :: VarSet
    interesting_ids = unionVarSets (map (transCalls M.empty) prop_ids)

    ids :: [Id]
    ids = varSetElems
            (filterVarSet
                (\ x -> not (fromPrelude x || isPropType x))
                interesting_ids)

    expr_str = "signature [" ++ intercalate "," entries ++ "]"

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

