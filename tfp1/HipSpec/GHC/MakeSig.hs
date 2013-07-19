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

import Lang.Utils

import HipSpec.ParseDSL
import HipSpec.Heuristics.Calls
import HipSpec.Params

import Test.QuickSpec.Signature

makeSignature :: Params -> Map Name TyThing -> [Var] -> Ghc (Maybe Sig)
makeSignature p@Params{..} named_things prop_ids = do

    liftIO $ do
        whenFlag p PrintAutoSig $ putStrLn (expr_str "\n\t,")
        whenFlag p DebugAutoSig $ do
            putStrLn $ "--extra=" ++ show extra' ++ ":" ++ showOutputable extra_ids
            putStrLn $ "--extra-trans=" ++ show extra_trans' ++ ":" ++ showOutputable extra_trans_ids
            putStrLn $ "Prop ids: " ++ showOutputable prop_ids ++ " (only=" ++ show only ++ ")"
            putStrLn $ "Transitive ids: " ++ showOutputable interesting_ids
            putStrLn $ "Final ids: " ++ showOutputable ids

    if length entries < 3
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (expr_str ",")
  where
    rm_newlines = unwords . lines

    extra' = concatMap (splitOn ",") extra
    extra_trans' = concatMap (splitOn ",") extra_trans

    named_things' :: Map String Id
    named_things' = M.fromList . mapMaybe (uncurry t) . M.toList $ named_things
      where
        t :: Name -> TyThing -> Maybe (String,Id)
        t n (AnId i)      | not (junk i) = Just (nameToString n,i)
        t n (ADataCon dc) = Just (nameToString n,dataConWorkId dc)
        t _ _             = Nothing

    extra_trans_ids :: [Id]
    extra_trans_ids = mapMaybe (`M.lookup` named_things') extra_trans'

    interesting_ids :: VarSet
    interesting_ids = unionVarSets $
        map (transCalls With) (prop_ids ++ extra_trans_ids)

    extra_ids :: [Id]
    extra_ids = mapMaybe (`M.lookup` named_things') extra'

    junk :: Id -> Bool
    junk x = or [ m `isInfixOf` s
                | m <- ["Control.Exception","GHC.Prim","GHC.Types.Int","GHC.List","GHC.Num"]
                , s <- [showOutputable x,showOutputable (varType x)]
                ]
    -- TODO: this junk list of junk could be removed by looking at things in scope instead

    ids :: [Id]
    ids = varSetElems $ filterVarSet (\ x -> not (fromPrelude x || varWithPropType x || junk x)) $
            interesting_ids `unionVarSet` mkVarSet extra_ids

    expr_str x = "signature [" ++ intercalate x (map rm_newlines entries) ++ "]"

    entries =
        [ unwords
            [ "Test.QuickSpec.Signature.fun" ++ show (varArity i)
            , show (varToString i)
            , "(" ++ showOutputable i ++ ")"
            ]
        | i <- ids
        ] ++
        [ unwords
            [ {- if pvars then "pvars" else -} "vars"
            , show ["x","y","z"]
            , "(Prelude.undefined :: " ++ showOutputable t ++ ")"
            ]
        | t <- types
        ] ++
        [ "Test.QuickSpec.Signature.withTests " ++ show tests
        , "Test.QuickSpec.Signature.withQuickCheckSize " ++ show quick_check_size
        , "Test.QuickSpec.Signature.withSize " ++ show size
        ]

    types = nubBy eqType $ concat
        [ ty : tys
        | i <- ids
        , let (tys,ty) = splitFunTys (varType i)
        ]

varArity :: Var -> Int
varArity = length . fst . splitFunTys . varType

