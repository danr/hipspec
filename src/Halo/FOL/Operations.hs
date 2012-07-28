{-# LANGUAGE PatternGuards,ScopedTypeVariables,FlexibleContexts #-}
module Halo.FOL.Operations where

import Halo.FOL.Internals.Internals

import Data.Generics.Geniplate

import qualified Data.Set as S
import Data.Set (Set)

replaceVarsTm :: (v -> u) -> Term q v -> Term q u
replaceVarsTm k = go
  where
    go tm = case tm of
        Fun v as   -> Fun (k v) (map go as)
        Ctor v as  -> Ctor (k v) (map go as)
        Skolem v   -> Skolem (k v)
        App t1 t2  -> App (go t1) (go t2)
        Proj i v a -> Proj i (k v) (go a)
        Ptr v      -> Ptr (k v)
        QVar q     -> QVar q

replaceQVarsTm :: (q -> r) -> Term q v -> Term r v
replaceQVarsTm k = go
  where
    go tm = case tm of
        Fun v as   -> Fun v (map go as)
        Ctor v as  -> Ctor v (map go as)
        Skolem v   -> Skolem v
        App t1 t2  -> App (go t1) (go t2)
        Proj i v a -> Proj i v (go a)
        Ptr v      -> Ptr v
        QVar q     -> QVar (k q)

formulaMapTerms :: (Term q v -> Term r u) -> (q -> r)
                -> Formula q v -> Formula r u
formulaMapTerms tm qv = go
  where
    go f = case f of
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

allSymbols :: forall f q v . (UniverseBi (f q v) (Term q v),Ord v)
           => f q v -> [v]
allSymbols = S.toList . S.unions . map get . universeBi
  where
    get :: Term q v -> Set v
    get (Fun v _)    = S.singleton v
    get (Ctor v _)   = S.singleton v
    get (Skolem v)   = S.singleton v
    get (Proj _ v _) = S.singleton v
    get (Ptr v)      = S.singleton v
    get _            = S.empty

allQuant :: forall f q v . (UniverseBi (f q v) (Formula q v)
                           ,UniverseBi (f q v) (Term q v)
                           ,Ord q)
         => f q v -> [q]
allQuant phi = S.toList . S.unions $
    map getTm (universeBi phi) ++ map getFm (universeBi phi)
  where
    getTm :: Term q v -> Set q
    getTm (QVar v) = S.singleton v
    getTm _        = S.empty

    getFm :: Formula q v -> Set q
    getFm (Forall qs _) = S.fromList qs
    getFm _             = S.empty

substVars :: forall f q v . (TransformBi (Term q v) (f q v),Eq v)
          => v -> v -> f q v -> f q v
substVars old new = rewriteBi s
  where
    s :: Term q v -> Maybe (Term q v)
    s (Fun v as)   | v == old = Just (Fun new as)
    s (Ctor v as)  | v == old = Just (Ctor new as)
    s (Proj i v a) | v == old = Just (Proj i new a)
    s (Ptr v)      | v == old = Just (Ptr new)
    s _                       = Nothing

substQVar :: forall f q v . (TransformBi (Term q v) (f q v),Eq q)
          => q -> q -> f q v -> f q v
substQVar old new = rewriteBi s
  where
    s :: Term q v -> Maybe (Term q v)
    s (QVar v) | v == old = Just (QVar new)
    s _                   = Nothing

rewriteBi :: forall s t . (TransformBi s s,TransformBi s t) => (s -> Maybe s) -> t -> t
rewriteBi f = transformBi g
  where
    g :: s -> s
    g x = maybe x (rewriteBi f) (f x)
