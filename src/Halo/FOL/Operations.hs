{-# LANGUAGE PatternGuards,ScopedTypeVariables #-}
module Halo.FOL.Operations where

import Halo.FOL.Internals.Internals
import Halo.Util (nubSorted)

import Data.Generics.Uniplate.Data
import Data.Data
import Data.Maybe

replaceVarsTm :: (v -> u) -> Term q v -> Term q u
replaceVarsTm k = go
  where go tm = case tm of
             Fun v as   -> Fun (k v) (map go as)
             Ctor v as  -> Ctor (k v) (map go as)
             App t1 t2  -> App (go t1) (go t2)
             Proj i v a -> Proj i (k v) (go a)
             Ptr v      -> Ptr (k v)
             QVar q     -> QVar q
             Constant c -> Constant c

replaceQVarsTm :: (q -> r) -> Term q v -> Term r v
replaceQVarsTm k = go
  where go tm = case tm of
             Fun v as   -> Fun v (map go as)
             Ctor v as  -> Ctor v (map go as)
             App t1 t2  -> App (go t1) (go t2)
             Proj i v a -> Proj i v (go a)
             Ptr v      -> Ptr v
             QVar q     -> QVar (k q)
             Constant c -> Constant c

formulaMapTerms :: (Term q v -> Term r u) -> (q -> r)
                -> Formula q v -> Formula r u
formulaMapTerms tm qv = go
  where go f = case f of
             Equal t1 t2   -> Equal (tm t1) (tm t2)
             Unequal t1 t2 -> Unequal (tm t1) (tm t2)
             And fs        -> And (map go fs)
             Or fs         -> Or (map go fs)
             Implies f1 f2 -> Implies (go f1) (go f2)
             Neg f'        -> Neg (go f')
             Forall qs f'  -> Forall (map qv qs) (go f')
             Exists qs f'  -> Exists (map qv qs) (go f')
             CF t          -> CF (tm t)
             Min t         -> Min (tm t)
             MinRec t      -> MinRec (tm t)

clauseMapTerms :: (Term q v -> Term r u) -> (q -> r)
               -> Clause q v -> Clause r u
clauseMapTerms tm qv cl = case cl of
    Clause c s f -> Clause c s (formulaMapTerms tm qv f)
    Comment s    -> Comment s

allSymbols :: forall f q v . (Data (f q v),Data q,Data v,Ord v) => f q v -> [v]
allSymbols = nubSorted . mapMaybe get . universeBi
  where
    get :: Term q v -> Maybe v
    get (Fun v _)    = Just v
    get (Ctor v _)   = Just v
    get (Proj _ v _) = Just v
    get (Ptr v)      = Just v
    get _            = Nothing

allQuant :: forall f q v . (Data (f q v),Data q,Data v,Ord q) => f q v -> [q]
allQuant phi = nubSorted (mapMaybe getTm (universeBi phi)
                    ++ concatMap getFm (universeBi phi))
  where
    getTm :: Term q v -> Maybe q
    getTm (QVar v) = Just v
    getTm _        = Nothing

    getFm :: Formula q v -> [q]
    getFm (Forall qs _) = qs
    getFm _             = []

substVars :: forall f q v . (Data (f q v),Data q,Data v,Eq v)
          => v -> v -> f q v -> f q v
substVars old new = rewriteBi s
  where
    s :: Term q v -> Maybe (Term q v)
    s (Fun v as)   | v == old = Just (Fun new as)
    s (Ctor v as)  | v == old = Just (Ctor new as)
    s (Proj i v a) | v == old = Just (Proj i new a)
    s (Ptr v)      | v == old = Just (Ptr new)
    s _                       = Nothing

substQVar :: forall f q v . (Data (f q v),Data q,Data v,Eq q)
         => q -> q -> f q v -> f q v
substQVar old new = rewriteBi s
  where
    s :: Term q v -> Maybe (Term q v)
    s (QVar v) | v == old = Just (QVar new)
    s _                   = Nothing
