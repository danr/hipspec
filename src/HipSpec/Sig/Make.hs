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
import HipSpec.Sig.Resolve
import HipSpec.Sig.Symbols
import HipSpec.Lang.CoreToRich
import HipSpec.Lang.Type(DB(..))

import Test.QuickSpec.Signature
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils

import Control.Monad
import Outputable
import qualified Data.Map as Map
import Data.Ord

{-

    [Note unqualified identifiers]

    Identifiers to be put as function in the signature needs to be in scope
    unqualified, i.e. length works, but not List.length.

    makeResolveMap in Resolve wants to parse these strings in the signature

-}

makeSignature :: Params -> Maybe Var -> [Var] -> Ghc ([(Sig, [[(Int, Type)]])],Maybe Type)
makeSignature p@Params{..} cond_id prop_ids = do

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

    m_a_ty <- getA

    let a_ty = case m_a_ty of
            Just ty -> ty
            Nothing -> error "Test.QuickSpec.Prelude.A not in scope!"

        mono = monomorphise a_ty

    try <- case cond_id of
        Nothing -> return Nothing
        Just i | isabelle_mode -> case splitFunTy_maybe (mono (varType i)) of
            Just (_def,rest) -> return (Just rest)
            _ -> error $ "Predicate " ++ cond_name ++ " is of wrong type, " ++ showOutputable (varType i) ++ ", (not Default -> X -> Bool)"
        Just i -> return (Just (mono (varType i)))

    Just sig <- makeSigFrom p ids_in_scope mono []
    rm <- makeResolveMap p sig

    let tries = case try of
            Nothing -> [[]]
            Just ty -> make_tries sig rm cond_count cond_name ty

    sigs <- catMaybes <$> mapM (makeSigFrom p ids_in_scope mono) tries

    return (zip sigs (map (map snd) tries), try)

make_tries :: Sig -> ResolveMap -> Int -> String -> Type -> [[(String, [(Int, Type)])]]
make_tries sig rm cond_count cond_name ty =
  [ [(cond_name, vs) | vs <- vss]
  | vss <- sortBy (comparing length) (nubBy eq (clauses cond_count (make_try_vars sig rm ty)))]
  where
    eq xs ys = null (xs' \\ ys') && null (ys' \\ xs')
      where
        xs' = map tr xs
        ys' = map tr ys
        tr xs = [ (x, fmap DB (trType y)) | (x, y) <- xs ]

clauses :: Int -> [[(Int, Type)]] -> [[[(Int, Type)]]]
clauses = aux Map.empty
  where
    aux _ 0 _ = [[]]
    aux seen n xs = [[]] `mplus` do
      (i, x) <- zip [0..] xs
      let ys = [ (ty, [ v | (v, ty') <- x, DB ty == DB (either error id (trType ty')) ])
               | DB ty <- usort (map (DB . either error id . trType . snd) x) ]
      guard (all (ok seen) ys)
      fmap (x:) (aux (foldr update seen ys) (n-1) (take i xs ++ drop (i+1) xs))

    ok seen (ty, vs) =
      ascending (nub (filter (> n) vs))
      where
        n = Map.findWithDefault (-1) ty seen
        ascending xs = xs == [n+1..n+length xs]

    update (ty, vs) seen =
      Map.insertWith max ty (maximum vs) seen

make_try_vars :: Sig -> ResolveMap -> Type -> [[(Int, Type)]]
make_try_vars sig rm ty =
  case splitFunTy_maybe ty of
    Nothing -> [[]]
    Just (arg, rest) -> do
      vars' <- make_try_vars sig rm rest
      n <- [0..varCount sig rm arg-1]
      return ((n, arg):vars')

varCount :: Sig -> ResolveMap -> Type -> Int
varCount sig rm ty =
  case [some (length . unO) vs | vs <- TypeMap.toList (variables sig), either error id (trType ty) == typeRepToType rm (someType vs) ] of
    n:_ -> n
    _ -> 0

getA :: Ghc (Maybe Type)
getA = do

    a_things <- lookupString "Test.QuickSpec.Prelude.A"

    return $ listToMaybe
        [ mkTyConTy tc
        | ATyCon tc <- a_things
        ]

backupNames :: [String]
backupNames = ["x","y","z"]

-- Monomorphise a type and determine what names variables should have for it
nameType :: Params -> (Type -> Type) -> Type -> Ghc (Type,[String])
nameType p@Params{..} mono (mono -> t) = handleSourceError handle $ do

    -- Try to get the names from the instance
    let t_str     = "(" ++ showOutputable t ++ ")"
        names_str = "HipSpec.names ((let _x = _x in _x) :: " ++ rmNewlines t_str ++ ")"
    liftIO $ whenFlag p DebugAutoSig $ putStrLn $ "names_str:" ++ names_str
    m_names :: Maybe [String] <- fromDynamic `fmap` dynCompileExpr names_str

    names <- case m_names of
        -- With isabelle_mode, allow one identifier, "_", for Default
        Just xs | isabelle_mode -> return xs

        -- Otherwise, warn if there aren't three identifiers and pad or crop
        Just xs -> do
            let res = take 3 (xs ++ backupNames)
            when (length xs /= 3 && verbosity > 0) $ liftIO $ putStrLn $
                "Warning: Names instance for " ++ t_str ++
                " does not have three elements, defaulting to " ++ show res
            return res
        Nothing -> return backupNames

    return (t,names)
  where
    handle e = do
        let flat_str = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ') . unwords . words
            e_str = case splitOn "arising from" (show e) of
                x:_ -> flat_str x
                []  -> ""
        when (verbosity > 0 ) $ liftIO $
            putStrLn $ "Warning: " ++ e_str ++ ", defaulting to " ++ show backupNames
        return (t,backupNames)

data VarDesc = VarDesc [String] Type {-^ should be monomorphic already -}

stringVarDesc :: Params -> VarDesc -> String
stringVarDesc Params{..} (VarDesc xs t) =
    unwords
      [ if pvars then "pvars" else "vars"
      , show xs
      , "("
      , "(let _x = _x in _x)"
      , "::"
      , showOutputable t
      , ")"
      ]

makeSigFrom :: Params -> [Var] -> (Type -> Type) -> [(String, [(Int, Type)])] -> Ghc (Maybe Sig)
makeSigFrom p@Params{..} ids mono cond_info = do

    let types = nubBy eqType $ concat
            [ ty : tys
            | i <- ids
            , let (tys,ty) = splitFunTys (mono (varType i))
            ]

    named_mono_types <- mapM (nameType p mono) types

    let var_desc =
            [ VarDesc names t | (t,names) <- named_mono_types]

    let fun | isabelle_mode = "obs"
            | otherwise = "Test.QuickSpec.Signature.fun"
        entries =
            [ unwords
                [ fun ++ show (varArity mono i)
                , show (varToString i)  -- see Note unqualified identifiers
                , "("
                , "(" ++ varToString i ++ ")"
                , "::"
                , showOutputable (mono (varType i))
                , ")"
                ]
            | i <- ids
            , not isabelle_mode || varToString i /= "Default" -- Don't add the default constructor
            ] ++
            [ "Test.QuickSpec.Signature.withCondition (\\sig val -> (" ++ cond ++ ")" ++
              concat [ " (error \"Predicate can't be partial\")" | isabelle_mode ] ++
              concat [ " (evalVar sig " ++ show x ++ " val)" | x <- map fst xs ] ++ ")"
            | (cond, xs) <- cond_info ] ++
            map (stringVarDesc p) var_desc ++
            [ "Test.QuickSpec.Signature.withTests " ++ show tests
            , "Test.QuickSpec.Signature.withQuickCheckSize " ++ show quick_check_size
            , "Test.QuickSpec.Signature.withSize " ++ show size
            ]

        expr_str x = "signature [" ++ intercalate x (map rmNewlines entries) ++ "]"

    liftIO $ whenFlag p PrintAutoSig $ putStrLn (expr_str "\n    ,")

    if length entries < 3
        then return Nothing
        else fromDynamic `fmap` dynCompileExpr (expr_str ",")

rmNewlines :: String -> String
rmNewlines = unwords . lines

varArity :: (Type -> Type) -> Var -> Int
varArity mono = length . fst . splitFunTys . snd . splitForAllTys . mono . varType

-- Monomorphises (instantiates all foralls with the first argument)
-- *Also removes contexts*
monomorphise :: Type -> Type -> Type
monomorphise mono_ty orig_ty = applyTys class_stripped_ty (zipWith const (repeat mono_ty) tvs)
  where
    (tvs, rho_ty) = splitForAllTys orig_ty

    class_stripped_ty = mkForAllTys tvs (rmClass rho_ty)

