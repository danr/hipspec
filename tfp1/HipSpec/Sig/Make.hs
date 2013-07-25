{-# LANGUAGE RecordWildCards,PatternGuards #-}
module HipSpec.Sig.Make (makeSignature) where

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

import HipSpec.GHC.Utils
import HipSpec.Sig.Scope
import HipSpec.ParseDSL
import HipSpec.GHC.Calls
import HipSpec.Params

import Test.QuickSpec.Signature

import Control.Monad

makeSignature :: Params -> Map Name TyThing -> [Var] -> Ghc (Maybe Sig)
makeSignature p@Params{..} named_things prop_ids = do

    let in_scope x = do
            a <- inScope (showOutputable x)
            b <- inScope (varToString x)
            return (a || b)

    ids <- filterM in_scope ids0

    let a_id = "Test.QuickSpec.Prelude.A"

    xs <- parseName a_id

    let mono = monomorphise a_ty

        a_cands = [ mkTyConTy tc
                  | a <- xs
                  , Just (ATyCon tc) <- [M.lookup a named_things]
                  ]

        a_ty = case a_cands of
            x:_ -> x
            _   -> error $ a_id ++ " not in scope!"

    let entries =
            [ unwords
                [ "Test.QuickSpec.Signature.fun" ++ show (varArity i)
                , show (varToString i)
                , "("
                , "(" ++ rmGHCTypes (showOutputable i) ++ ")"
                , "::"
                , showOutputable (mono (varType i))
                , ")"
                ]
            | i <- ids
            ] ++
            [ unwords
                [ {- if pvars then "pvars" else -} "vars"
                , show ["x","y","z"]
                , "("
                , "Prelude.undefined"
                , "::"
                , showOutputable (mono t)
                , ")"
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
            , let (tys,ty) = splitFunTys (mono (varType i))
            ]

        expr_str x = "signature [" ++ intercalate x (map rm_newlines entries) ++ "]"

    liftIO $ do
        whenFlag p PrintAutoSig $ putStrLn (expr_str "\n\t,")
        whenFlag p DebugAutoSig $ do
            putStrLn $ "--extra=" ++ show extra' ++ ":" ++ showOutputable extra_ids
            putStrLn $ "--extra-trans=" ++ show extra_trans' ++ ":" ++ showOutputable extra_trans_ids
            putStrLn $ "Prop ids: " ++ showOutputable prop_ids ++ " (only=" ++ show only ++ ")"
            putStrLn $ "Transitive ids: " ++ showOutputable interesting_ids
            putStrLn $ "Init ids: " ++ showOutputable ids0
            putStrLn $ "Final ids: " ++ showOutputable ids

    if length entries < 3
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (expr_str ",")
  where
    rm_newlines = unwords . lines

    extra' = concatMap (splitOn ",") extra
    extra_trans' = concatMap (splitOn ",") extra_trans

    -- TODO: Make this a multi-set or filter out things that are not in scope
    -- Currently, it prefers GHC.Num.+ instead of + that is in scope
    --            and GHC.List.length instead of length that is in scope
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

    -- TODO: This could be removed if named_things' was fixed
    junk :: Id -> Bool
    junk x = or [ m `isInfixOf` s
                | m <- ["Control.Exception","GHC.Prim","GHC.Types.Int","GHC.List","GHC.Num"]
                , s <- [showOutputable x,showOutputable (varType x)]
                ]

    -- Ids, but not necessarily in scope
    ids0 :: [Id]
    ids0 = varSetElems $ filterVarSet (\ x -> not (fromPrelude x || varWithPropType x || junk x)) $
            interesting_ids `unionVarSet` mkVarSet extra_ids

varArity :: Var -> Int
varArity = length . fst . splitFunTys . snd . splitForAllTys . varType

monomorphise :: Type -> Type -> Type
monomorphise mono_ty orig_ty = applyTys orig_ty (zipWith const (repeat mono_ty) tvs)
  where
    (tvs, _rho_ty) = splitForAllTys orig_ty

-- | Cons, nil etc curiously start with GHC.Types., so we drop it
rmGHCTypes :: String -> String
rmGHCTypes ('G':'H':'C':'.':'T':'y':'p':'e':'s':'.':s) = s
rmGHCTypes s                                           = s

