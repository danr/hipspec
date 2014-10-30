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
import qualified HipSpec.Lang.CoreToRich as CTR

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
        Rewriting.Var tv               -> S.TyVar (QSTyVar tv)
        Rewriting.Fun QS.Arrow [a,b]   -> go a `S.ArrTy` go b
        Rewriting.Fun (QS.TyCon tc) as ->
            let tc' = lookupTyCon m tc
            in if CTR.essentiallyInteger tc'
                then S.Integer
                else S.TyCon (idFromTyCon tc') (map go as)

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

isabelleFunctionNames :: [(String, String)]
isabelleFunctionNames =
  [(":", "#"),
   ("++", "@"),
   ("reverse", "rev"),
   ("plus_nat", "Groups.plus_class.plus"),
   ("Zero_nat", "Groups.zero_class.zero"),
   ("one_nat", "Groups.one_class.one")]
