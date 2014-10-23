{-# LANGUAGE RecordWildCards,PatternGuards,ScopedTypeVariables,ViewPatterns,CPP #-}
module HipSpec.Sig.Make (makeSignature) where

import Data.List.Split (splitOn)

import CoreMonad
import GHC hiding (Sig)
import Type
import Var

import Data.Dynamic
import Data.List
import Data.Maybe

import HipSpec.GHC.Utils
import HipSpec.Sig.Scope
import HipSpec.ParseDSL
import HipSpec.GHC.Calls
import HipSpec.Params
import HipSpec.Utils

import QuickSpec.Signature

import Control.Monad
import Outputable

makeSignature :: Params -> [Var] -> Ghc [Signature]
makeSignature p@Params{..} prop_ids = do

    let extra' = concatMap (splitOn ",") extra
        extra_trans' = concatMap (splitOn ",") extra_trans

    extra_trans_things <- concatMapM lookupString extra_trans'

    let extra_trans_ids = mapMaybe thingToId extra_trans_things

        trans_ids :: VarSet
        trans_ids = unionVarSets $
            map (transCalls With) (prop_ids ++ extra_trans_ids)

    extra_things <- concatMapM lookupString extra'

    let extra_ids = mapMaybe thingToId extra_things

        ids = varSetElems $ filterVarSet (\ x -> not (varFromPrelude x || varWithPropType x))
            trans_ids `unionVarSet` mkVarSet extra_ids

    -- Filters out silly things like
    -- Control.Exception.Base.patError and GHC.Prim.realWorld#
    let in_scope = inScope . varToString -- see Note unqualified identifiers

    ids_in_scope <- filterM in_scope ids

    liftIO $ whenFlag p DebugAutoSig $ do
        let out :: Outputable a => String -> a -> IO ()
            out lbl o = putStrLn $ lbl ++ " =\n " ++ showOutputable o
#define OUT(i) out "i" (i)
        OUT(extra_trans_things)
        OUT(extra_trans_ids)
        OUT(trans_ids)
        OUT(extra_things)
        OUT(extra_ids)
        OUT(ids)
        OUT(ids_in_scope)
#undef OUT

    tyvars <- magicTyVars

    msig <- makeSigFrom p ids_in_scope (polymorphise tyvars)

    return (maybeToList msig)

makeSigFrom :: Params -> [Var] -> (Type -> Type)  -> Ghc (Maybe Signature)
makeSigFrom p ids poly = do
    liftIO $ whenFlag p PrintAutoSig $ putStrLn expr_str
    if null constants
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (oneliner expr_str)
  where
    constants =
        [ unwords
            [ "QuickSpec.Signature.constant"
            , show (varToString i)
            , par $
                par (varToString i) ++ " :: " ++
                showOutputable (poly (varType i))
            ]
        | i <- ids
        ]

    base_types = nubBy eqType (concatMap (baseTypes . varType) ids)
    instances =
        [ unwords
            [ "QuickSpec.Signature.baseType"
            , par ("undefined :: " ++ showOutputable t)
            ]
        | t <- base_types
        ]

    expr_str = unlines $
        [ "signature" ] ++
        ind (["{ constants ="] ++ ind (list constants) ++
             [", instances ="] ++ ind (list instances) ++
             ["}"])

list :: [String] -> [String]
list xs0 = case map oneliner xs0 of
    []   -> ["[]"]
    x:xs -> ["[ " ++ x] ++ [", " ++ y | y <- xs] ++ ["]"]


par :: String -> String
par s = "(" ++ s ++ ")"

ind :: [String] -> [String]
ind = map ("  "++)

oneliner :: String -> String
oneliner = unwords . lines

baseTypes :: Type -> [Type]
baseTypes t0
    | Just (t1,t2) <- splitFunTy_maybe t0    = me $ baseTypes t1 ++ baseTypes t2
    | Just (tc,ts) <- splitTyConApp_maybe t0 = me $ concatMap baseTypes ts
    | Just (tvs,t) <- splitForAllTy_maybe t0 = me $ baseTypes t
    | otherwise                              = me []
  where
    me | isBase t0 = (t0:)
       | otherwise = id

isBase :: Type -> Bool
isBase t
    | Just (tc,ts) <- splitTyConApp_maybe t = not (isFunTyCon tc) && all isBase ts
    | otherwise                             = False


magicTyVars :: Ghc [Type]
magicTyVars = concatMapM
    (\ i -> do
        things <- lookupString ("QuickSpec.Type." ++ i)
        return [mkTyConTy tc | ATyCon tc <- things])
    ["A","B","C","D"]


-- | Change forall-quantified variables into QuickSpec's magic type variables
polymorphise :: [Type] -> Type -> Type
polymorphise tyvars orig_ty = applyTys class_stripped_ty (zipWith const (cycle tyvars) tvs)
  where
    (tvs, rho_ty) = splitForAllTys orig_ty

    -- removes contexts
    class_stripped_ty = mkForAllTys tvs (rmClass rho_ty)

