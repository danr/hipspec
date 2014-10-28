{-# LANGUAGE RecordWildCards,PatternGuards,ScopedTypeVariables,ViewPatterns,CPP,NamedFieldPuns #-}
module HipSpec.Sig.Make (makeSignature) where

import Data.List.Split (splitOn)

import CoreMonad
import GHC hiding (Sig)
import Type
import Var

import Data.Dynamic (fromDynamic)
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

parseToId :: String -> Ghc Id
parseToId s = do
    t <- lookupString s
    case mapMaybe thingToId t of
        []  -> error $ s ++ " not in scope!"
        [x] -> return x
        xs  -> error $ s ++ " in scope as too many things: " ++ showOutputable xs

makeSignature :: Params -> [Var] -> Ghc [Signature]
makeSignature p@Params{..} prop_ids = do

    extra_trans_ids <- mapM parseToId (concatMap (splitOn ",") extra_trans)

    let trans_ids :: VarSet
        trans_ids = unionVarSets $
            map (transCalls With) (prop_ids ++ extra_trans_ids)

    extra_ids <- mapM parseToId (concatMap (splitOn ",") extra)

    let ids = varSetElems $ filterVarSet (\ x -> not (varFromPrelude x || varWithPropType x))
            trans_ids `unionVarSet` mkVarSet extra_ids

    -- Filters out silly things like
    -- Control.Exception.Base.patError and GHC.Prim.realWorld#
    let in_scope = inScope . varToString -- see Note unqualified identifiers

    ids_in_scope <- filterM in_scope ids

    liftIO $ whenFlag p DebugAutoSig $ do
        let out :: Outputable a => String -> a -> IO ()
            out lbl o = putStrLn $ lbl ++ " =\n " ++ showOutputable o
#define OUT(i) out "i" (i)
        OUT(extra_trans_ids)
        OUT(extra_ids)
        OUT(ids)
        OUT(ids_in_scope)
#undef OUT

    tyvars <- magicTyVars

    msig <- makeSigFrom p ids_in_scope (polymorphise tyvars)

    return (maybeToList msig)

makeSigFrom :: Params -> [Var] -> (Type -> Type)  -> Ghc (Maybe Signature)
makeSigFrom p@Params{qspruner,termsize} ids poly = do
    liftIO $ whenFlag p PrintAutoSig $ putStrLn expr_str
    if null constants
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (oneliner expr_str)
  where
    sg s = "QuickSpec.Signature." ++ s
    cs s = "Data.Constraint." ++ s

    constants =
        [ unwords
            [ sg "constant"
            , show (varToString i)
            , par $
                par (varToString i) ++ " :: " ++
                showOutputable (poly (varType i))
            ]
        | i <- ids
        ]

    instances =
        [ unwords
            [ sg ("inst" ++ concat [ show (length tvs) | length tvs >= 2 ])
            , par $ unwords
                [ cs "Sub", cs "Dict", "::"
                , par (intercalate "," (map pp pre))
                , cs ":-", pp post
                ]
            ]
        | tc <- nub (concatMap (tycons . varType) ids)
        , let tvs = tyConTyVars tc
--        , not (null tvs)
        , let tvs_ty = map mkTyVarTy tvs
        , let t = mkForAllTys tvs (tvs_ty `mkFunTys` mkTyConApp tc tvs_ty)
        , let (pre,post) = splitFunTys (poly t)
        , cls <- ["Prelude.Ord","Test.QuickCheck.Arbitrary"]
        , let pp x = cls ++ " " ++ par (showOutputable x)
        ]

    expr_str = unlines $
        [ "signature" ] ++
        ind (["{ constants ="] ++ ind (list constants) ++
             [", instances ="] ++ ind (list instances) ++
             [", extraPruner = Prelude.Just QuickSpec.Signature.None" | not qspruner] ++
             [", maxTermSize = Prelude.Just " ++ show termsize] ++
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

tycons :: Type -> [TyCon]
tycons t0
    | Just (t1,t2) <- splitFunTy_maybe t0    = tycons t1 `union` tycons t2
    | Just (tc,ts) <- splitTyConApp_maybe t0 = tc : nub (concatMap tycons ts)
    | Just (tvs,t) <- splitForAllTy_maybe t0 = tycons t
    | otherwise                              = []

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

