{-# LANGUAGE ParallelListComp, ViewPatterns, PatternGuards, ScopedTypeVariables, RecordWildCards, NamedFieldPuns #-}
-- | Translating from QuickSpec -> Core/HipSpec
module HipSpec.Sig.QSTerm (trProp) where

import QuickSpec.Type as QS
import QuickSpec.Term as QS
import QuickSpec.Prop as QS
import QuickSpec.Pretty as QS
import QuickSpec.Signature as QS
import qualified Data.Rewriting.Term as Rewriting

import HipSpec.Read (SigInfo(..))
import HipSpec.Sig.Resolve
import HipSpec.Utils
import HipSpec.Property as P
import qualified HipSpec.Lang.Simple as S

import HipSpec.Params

import Data.List (union)

import HipSpec.Id

import Control.Monad

trTerm :: ResolveMap -> QS.Term -> S.Expr Id
trTerm m = go
  where
    go t = case t of
        Rewriting.Var v    -> S.Lcl (QSVariable v) (trType m (typ v))
        Rewriting.Fun c as ->
            let (ghc_var,pt) = lookupCon m c
            in  case match pt (trType m (typ c)) of
                    Just ts -> S.Gbl (idFromVar (ghc_var)) pt ts `S.apply` map go as
                    Nothing -> error $ "Incorrect type application " ++ show t

trType :: ResolveMap -> QS.Type -> S.Type Id
trType m = go
  where
    go t0 = case t0 of
        Rewriting.Fun QS.Arrow [a,b]   -> go a `S.ArrTy` go b
        Rewriting.Fun (QS.TyCon tc) as -> S.TyCon (idFromTyCon (lookupTyCon m tc)) (map go as)
        Rewriting.Var tv               -> S.TyVar (QSTyVar tv)

match :: Eq a => S.PolyType a -> S.Type a -> Maybe [S.Type a]
match (S.Forall tvs t) t' = sequence [ findTv tv t t' | tv <- tvs ]

findTv :: Eq a => a -> S.Type a -> S.Type a -> Maybe (S.Type a)
findTv x = go
  where
    go t t' = case (t,t') of
        (S.TyVar y    ,_)             | x == y -> return t'
        (S.ArrTy t1 t2,S.ArrTy s1 s2)          -> go t1 s1 `mplus` go t2 s2
        (S.TyCon a ts ,S.TyCon b ss)  | a == b -> msum (zipWith go ts ss)
        _                                      -> mzero

trLiteral :: ResolveMap -> QS.Literal QS.Term -> P.Literal
trLiteral m (a QS.:=: b) = trTerm m a P.:=: trTerm m b

literalFreeTyVars :: P.Literal -> [Id]
literalFreeTyVars (a P.:=: b) = S.exprFreeTyVars a `union` S.exprFreeTyVars b

trProp :: Params -> SigInfo -> Integer -> Prop -> Property
trProp Params{} SigInfo{..} i prop = Property
    { prop_name      = repr
    , prop_id        = QSPropId i
    , prop_origin    = P.QSProp prop
    , prop_tvs       = nubSorted $
        concatMap literalFreeTyVars plits ++
        [ QSTyVar tv | v <- occuring_vars, tv <- Rewriting.vars (typ v) ]
    , prop_vars      = [ (QSVariable v,trType m (typ v)) | v <- occuring_vars ]
    , prop_goal      = pgoal
    , prop_assums    = passums
    , prop_repr      = repr
    , prop_var_repr  = map QS.prettyShow occuring_vars
    }
  where
    prop' = QS.prettyRename sig prop

    repr = unwords (words (QS.prettyShow prop'))

    m :: ResolveMap
    m = resolve_map

    occuring_vars :: [QS.Variable]
    occuring_vars = nubSorted (concatMap Rewriting.vars (propTerms prop))

    plits@(pgoal:passums) = map (trLiteral m) (goal:assums)
      where assums :=>: goal = prop

{-
    mk_assum x = P.equalsTrue
        (S.Gbl v t ts `S.App` uncurry S.Lcl (lookupVar symbol_map x))
      where
        Just mono_ty = cond_mono_ty
        Just cd_id   = cond_id
        (v,t,ts) = translateId (either error id (CTR.trType mono_ty)) cd_id

    repr = show_eq e1 ++ eqls ++ show_eq e2
      where
        show_eq = show . mapVars (delBackquote . disambig) . mapConsts (on_name g)

        on_name h s = s { name = h (name s) }

        g x = case lookup x isabelleFunctionNames of
            Just y  | isabelle_mode -> y
            _                       -> x

        eqls | isabelle_mode = " = "
             | otherwise     = " == "

    final_repr = show_precond precond_vars repr

    raw_occuring_vars :: [Symbol]
    raw_occuring_vars = nubSorted (vars e1 ++ vars e2)

    disambig :: Symbol -> Symbol
    disambig = disambiguate sig (vars e1 ++ vars e2)

    occuring_vars :: [Symbol]
    occuring_vars = map delBackquote $ map disambig raw_occuring_vars

    precond_vars :: [Symbol]
    precond_vars = map delBackquote $ map disambig (filter isBackquoted raw_occuring_vars)

    term_to_expr = termToExpr symbol_map

    goal = term_to_expr e1 P.:=: term_to_expr e2

    show_precond [] u = u
    show_precond xs u = intercalate conj [ cond_name ++ " " ++ show x | x <- xs ] ++ " ==> " ++ u
      where
        conj | isabelle_mode = " & "
             | otherwise     = " && "

isBackquoted :: Symbol -> Bool
isBackquoted a = case name a of
    '`':_ -> True
    _     -> False

delBackquote :: Symbol -> Symbol
delBackquote a = case name a of
    '`':xs -> a { name = xs }
    _      -> a
    -}

isabelleFunctionNames :: [(String, String)]
isabelleFunctionNames =
  [(":", "#"),
   ("++", "@"),
   ("reverse", "rev"),
   ("plus_nat", "Groups.plus_class.plus"),
   ("Zero_nat", "Groups.zero_class.zero"),
   ("one_nat", "Groups.one_class.one")]
