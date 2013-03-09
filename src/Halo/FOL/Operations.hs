{-# LANGUAGE ScopedTypeVariables #-}
module Halo.FOL.Operations where

import Halo.FOL.Internals.Internals
import Halo.Util

import Data.Generics.Geniplate

import qualified Data.Set as S
import Data.Set (Set)

import Control.Arrow (first)
import Control.Monad (liftM)

replaceVarsTm :: (v -> u) -> Term q v t -> Term q u t
replaceVarsTm k = go
  where
    go tm = case tm of
        Fun v as    -> Fun (k v) (map go as)
        Ctor v as   -> Ctor (k v) (map go as)
        Skolem v t  -> Skolem (k v) t
        App t t1 t2 -> App t (go t1) (go t2)
        Proj i v a  -> Proj i (k v) (go a)
        Ptr v t     -> Ptr (k v) t
        QVar q      -> QVar q
        Prim p as   -> Prim p (map go as)
        Lit i       -> Lit i
        Bottom ty   -> Bottom ty

replaceQVarsTm :: (q -> r) -> Term q v t -> Term r v t
replaceQVarsTm k = go
  where
    go tm = case tm of
        Fun v as    -> Fun v (map go as)
        Ctor v as   -> Ctor v (map go as)
        Skolem v t  -> Skolem v t
        App t t1 t2 -> App t (go t1) (go t2)
        Proj i v a  -> Proj i v (go a)
        Ptr v t     -> Ptr v t
        QVar q      -> QVar (k q)
        Prim p as   -> Prim p (map go as)
        Lit i       -> Lit i
        Bottom ty   -> Bottom ty

formulaMapTerms :: (Term q v t -> Term r u t) -> (q -> r)
                -> Formula q v t -> Formula r u t
formulaMapTerms tm qv = go
  where
    go f = case f of
        Equal t1 t2   -> Equal (tm t1) (tm t2)
        Unequal t1 t2 -> Unequal (tm t1) (tm t2)
        And fs        -> And (map go fs)
        Or fs         -> Or (map go fs)
        Implies f1 f2 -> Implies (go f1) (go f2)
        Equiv f1 f2   -> Equiv (go f1) (go f2)
        Neg f'        -> Neg (go f')
        Forall qs f'  -> Forall (map (first qv) qs) (go f')
        Exists qs f'  -> Exists (map (first qv) qs) (go f')
        Total ty t    -> Total ty (tm t)

clauseMapTerms :: (Term q v t -> Term r u t) -> (q -> r)
               -> Clause q v t -> Clause r u t
clauseMapTerms tm qv cl = case cl of
    Clause c s f -> Clause c s (formulaMapTerms tm qv f)
    Comment s    -> Comment s

clauseMapFormula :: (Formula q v t -> Formula r u t)
                 -> Clause q v t -> Clause r u t
clauseMapFormula k cl = case cl of
    Clause c s f -> Clause c s (k f)
    Comment s    -> Comment s

allSymbols :: forall q v t . Ord v => Formula q v t -> [v]
allSymbols = S.toList . S.unions . map get . universeBi
  where
    get :: Term q v t -> Set v
    get (Fun v _)    = S.singleton v
    get (Ctor v _)   = S.singleton v
    get (Skolem v _) = S.singleton v
    get (Proj _ v _) = S.singleton v
    get (Ptr v _)    = S.singleton v
    get _            = S.empty

allSymbols' :: Ord v => Clause q v t -> [v]
allSymbols' (Clause _ _ f) = allSymbols f
allSymbols' (Comment _)    = []

allQuant :: forall q v t . Ord q => Formula q v t -> [q]
allQuant phi = S.toList . S.unions $
    map getTm (universeBi phi) ++ map getFm (universeBi phi)
  where
    getTm :: Term q v t -> Set q
    getTm (QVar v) = S.singleton v
    getTm _        = S.empty

    getFm :: Formula q v t -> Set q
    getFm (Forall qs _) = S.fromList (map fst qs)
    getFm _             = S.empty

allQuant' :: Ord q => Clause q v t -> [q]
allQuant' (Clause _ _ f) = allQuant f
allQuant' (Comment _ )   = []

substVars :: forall q v t . Eq v => v -> v -> Formula q v t -> Formula q v t
substVars old new = rewriteBi s
  where
    s :: Term q v t -> Maybe (Term q v t)
    s (Fun v as)   | v == old = Just (Fun new as)
    s (Ctor v as)  | v == old = Just (Ctor new as)
    s (Proj i v a) | v == old = Just (Proj i new a)
    s (Ptr v t)    | v == old = Just (Ptr new t)
    s _                       = Nothing

substQVar :: forall q v t . Eq q => q -> q -> Formula q v t -> Formula q v t
substQVar old new = rewriteBi s
  where
    s :: Term q v t -> Maybe (Term q v t)
    s (QVar v) | v == old = Just (QVar new)
    s _                   = Nothing

rewriteBi :: forall s t . (TransformBi s s,TransformBi s t) => (s -> Maybe s) -> t -> t
rewriteBi f = transformBi g
  where
    g :: s -> s
    g x = maybe x (rewriteBi f) (f x)

-- Querying

funsUsed :: forall q v t . Ord v => Clause q v t -> Set (v,Int)
funsUsed cl = S.fromList [ (f,length as) | Fun f as :: Term q v t <- universeBi cl ]

consUsed :: forall q v t . Ord v => Clause q v t -> Set (v,Int)
consUsed cl = S.fromList [ (c,length as) | Ctor c as :: Term q v t <- universeBi cl ]

ptrsUsed :: forall q v t . Ord v => Clause q v t -> Set v
ptrsUsed cl = S.fromList [ p | Ptr p _ :: Term q v t <- universeBi cl ]

primsUsed :: forall q v t . Ord v => Clause q v t -> Set Prim
primsUsed cl = S.fromList [ p | Prim p _ :: Term q v t <- universeBi cl ]

skolemsUsed :: forall q v t . Ord v => Clause q v t -> Set v
skolemsUsed cl = S.fromList [ s | Skolem s _ :: Term q v t <- universeBi cl ]

totalUsed :: forall q v t . Ord v =>  Clause q v t -> [t]
totalUsed cl = nubSorted [ t | Total t _ :: Formula q v t <- universeBi cl ]

appsUsed :: forall q v t . Ord t => [Formula q v t] -> [t]
appsUsed cl = nubSorted [ t | App t _ _ :: Term q v t <- universeBi cl ]

bottomsUsed :: forall q v t . Ord t => [Formula q v t] -> [t]
bottomsUsed cl = nubSorted [ t | Bottom t :: Term q v t <- universeBi cl ]


mapCl :: Monad m
       => (Formula q v t -> m (Formula q' v' t'))
       -> Clause q v t -> m (Clause q' v' t')
mapCl k (Clause s t f) = Clause s t `liftM` k f
mapCl _ (Comment s)    = return (Comment s)

