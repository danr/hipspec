{-# LANGUAGE RecordWildCards,PatternGuards,ScopedTypeVariables,ViewPatterns,CPP,NamedFieldPuns #-}
module HipSpec.Sig.Make (makeSignature,paramIds) where

import Data.List.Split (splitOn)

import CoreMonad
import GHC hiding (Sig)
import Type
import Var

import Data.Dynamic (fromDynamic)
import Data.List
import Data.Maybe

import HipSpec.GHC.Unfoldings
import HipSpec.GHC.Utils
import HipSpec.Sig.Scope
import HipSpec.ParseDSL
import HipSpec.GHC.Calls
import HipSpec.Params
import HipSpec.Utils

import QuickSpec.Signature

import Control.Monad
import Outputable

paramIds :: Params -> [Var] -> Ghc [Id]
paramIds p@Params{..} prop_ids = do
    extra_trans_ids <- mapM parseToId (concatMap (splitOn ",") extra_trans)

    let trans_ids :: VarSet
        trans_ids = unionVarSets $
            map (transCalls With) (prop_ids ++ extra_trans_ids)

    extra_ids <- mapM parseToId (concatMap (splitOn ",") extra)

    let ids = varSetElems $ filterVarSet (\ x -> not (varFromPrelude x || varWithPropType x) && not (hasClass (varType x)))
            trans_ids `unionVarSet` mkVarSet extra_ids

    -- Filters out silly things like
    -- Control.Exception.Base.patError and GHC.Prim.realWorld#
    let in_scope = inScope . varToString -- see Note unqualified identifiers

    ids_in_scope <- filterM in_scope ids

    liftIO $ whenFlag p DebugAutoSig $ do
        let out :: String -> [Id] -> IO ()
            out lbl os = putStrLn $ lbl ++ " =\n " ++ showOutputable [ (o{-,maybeUnfolding o-}) | o <- os ]
#define OUT(i) out "i" (i)
        OUT(prop_ids)
        OUT(extra_trans_ids)
        OUT(extra_ids)
        OUT(ids)
        OUT(ids_in_scope)
#undef OUT
    return ids_in_scope

parseToId :: String -> Ghc Id
parseToId s = do
    t <- lookupString s
    case mapMaybe thingToId t of
        []  -> error $ s ++ " not in scope!"
        [x] -> return x
        xs  -> error $ s ++ " in scope as too many things: " ++ showOutputable xs

makeSignature :: Params -> [Var] -> Ghc [Signature]
makeSignature p@Params{..} prop_ids = do

    ids <- paramIds p prop_ids

    tyvars <- magicTyVars

    msig <- makeSigFrom p ids (polymorphise tyvars)

    return (maybeToList msig)

makeSigFrom :: Params -> [Var] -> (Type -> Type)  -> Ghc (Maybe Signature)
makeSigFrom p@Params{..} ids poly = do
    liftIO $ whenFlag p PrintAutoSig $ putStrLn expr_str
    if null constants
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (oneliner expr_str)
  where
    sg s = "QuickSpec.Signature." ++ s
    cs s = "Data.Constraint." ++ s

    showy :: Outputable a => a -> String
    showy = go . showOutputable
      where
        go ('G':'H':'C':'.':'I':'n':'t':'e':'g':'e':'r':'.':'T':'y':'p':'e':'.':'I':'n':'t':'e':'g':'e':'r':s) = "Prelude.Integer" ++ go s
        go (x:xs) = x:go xs
        go [] = []

    constants =
        [ set_size i $ unwords
            [ sg "constant"
            , show (varToString i)
            , par $
                par (varToString i) ++ " :: " ++
                showy (poly (varType i))
            ]
        | i <- ids
        ]
      where
        set_size i | varArity poly i == 1 = con_size unarysize
                   | isDataConId i        = con_size consize
                   | otherwise            = id

        con_size x s = par s ++ " { QuickSpec.Term.conSize = " ++ show x ++ " }"

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
        , let tvs_ty = map mkTyVarTy tvs
        , let t = mkForAllTys tvs (tvs_ty `mkFunTys` mkTyConApp tc tvs_ty)
        , let (pre,post) = splitFunTys (poly t)
        , cls <- ["Prelude.Ord","Test.QuickCheck.Arbitrary"]
        , let pp x = cls ++ " " ++ par (showy x)
        ]

    expr_str = unlines $
        [ "QuickSpec.Signature.signature" ] ++
        ind (["{ QuickSpec.Signature.constants ="] ++ ind (list constants) ++
             [", QuickSpec.Signature.instances ="] ++ ind (list instances) ++
             [", QuickSpec.Signature.extraPruner = Prelude.Just " ++
                (if qspruner
                    then par "QuickSpec.Signature.SPASS 1"
                    else "QuickSpec.Signature.None")] ++
             [", QuickSpec.Signature.maxTermSize = Prelude.Just " ++ show termsize] ++
             [", QuickSpec.Signature.testTimeout = Prelude.Just 200000"] ++
             ["}"])

varArity :: (Type -> Type) -> Var -> Int
varArity poly = length . fst . splitFunTys . snd . splitForAllTys . poly . varType

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

