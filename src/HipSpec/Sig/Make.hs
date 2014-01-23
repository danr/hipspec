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

import Test.QuickSpec.Signature

import Control.Monad
import Outputable

{-

    [Note unqualified identifiers]

    Identifiers to be put as function in the signature needs to be in scope
    unqualified, i.e. length works, but not List.length.

    makeResolveMap in Resolve wants to parse these strings in the signature

-}

makeSignature :: Params -> [Var] -> Ghc (Maybe Sig)
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

    makeSigFrom p ids_in_scope =<< getA

getA :: Ghc (Maybe Type)
getA = do

    a_things <- lookupString "Test.QuickSpec.Prelude.A"

    return $ listToMaybe
        [ mkTyConTy tc
        | ATyCon tc <- a_things
        ]

makeSigFrom :: Params -> [Var] -> Maybe Type -> Ghc (Maybe Sig)
makeSigFrom p@Params{..} ids m_a_ty = do

    let a_ty = case m_a_ty of
            Just ty -> ty
            Nothing -> error "Test.QuickSpec.Prelude.A not in scope!"

        mono = monomorphise a_ty

        types = nubBy eqType $ concat
            [ ty : tys
            | i <- ids
            , let (tys,ty) = splitFunTys (mono (varType i))
            ]

        backup_names = ["x","y","z"]

        name_type :: Type -> Ghc (Type,[String])
        name_type (mono -> t) = handleSourceError handle $ do
            let t_str     = "(" ++ showOutputable t ++ ")"
                names_str = "HipSpec.names ((let _x = _x in _x) :: " ++ rmNewlines t_str ++ ")"
            liftIO $ whenFlag p DebugAutoSig $ putStrLn $ "names_str:" ++ names_str
            m_names :: Maybe [String] <- fromDynamic `fmap` dynCompileExpr names_str
            names <- case m_names of
                    Just xs -> do
                        let res = take 3 (xs ++ backup_names)
                        when (length xs /= 3 && verbosity > 0) $ liftIO $ putStrLn $
                            "Warning: Names instance for " ++ t_str ++
                            " does not have three elements, defaulting to " ++ show res
                        return res
                    Nothing -> return backup_names
            return (t,names)
          where
            handle e = do
                let flat_str = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ') . unwords . words
                    e_str = case splitOn "arising from" (show e) of
                        x:_ -> flat_str x
                        []  -> ""
                when (verbosity > 0 ) $ liftIO $
                    putStrLn $ "Warning: " ++ e_str ++ ", defaulting to " ++ show backup_names
                return (t,backup_names)

    named_mono_types <- mapM name_type types

    let entries =
            [ unwords
                [ "Test.QuickSpec.Signature.fun" ++ show (varArity i)
                , show (varToString i)  -- see Note unqualified identifiers
                , "("
                , "(" ++ varToString i ++ ")"
                , "::"
                , showOutputable (mono (varType i))
                , ")"
                ]
            | i <- ids
            ] ++
            [ unwords
                [ if pvars then "pvars" else "vars"
                , show names
                , "("
                , "(let _x = _x in _x)"
                , "::"
                , showOutputable t
                , ")"
                ]
            | (t,names) <- named_mono_types
            ] ++
            [ "Test.QuickSpec.Signature.withTests " ++ show tests
            , "Test.QuickSpec.Signature.withQuickCheckSize " ++ show quick_check_size
            , "Test.QuickSpec.Signature.withSize " ++ show size
            ]

        expr_str x = "signature [" ++ intercalate x (map rmNewlines entries) ++ "]"

    liftIO $ whenFlag p PrintAutoSig $ putStrLn (expr_str "\n    ,")

    if length entries < 3
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (expr_str ",")
  where

rmNewlines :: String -> String
rmNewlines = unwords . lines

varArity :: Var -> Int
varArity = length . fst . splitFunTys . snd . splitForAllTys . varType

monomorphise :: Type -> Type -> Type
monomorphise mono_ty orig_ty = applyTys orig_ty (zipWith const (repeat mono_ty) tvs)
  where
    (tvs, _rho_ty) = splitForAllTys orig_ty

