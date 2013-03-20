{-# LANGUAGE ScopedTypeVariables #-}
module Halo.FOL.Operations where

import Halo.FOL.Internals.Internals
import Halo.Util

import Data.Generics.Geniplate

import qualified Data.Set as S
import Data.Set (Set)

import Data.Maybe

-- import Control.Monad (liftM)

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
allQuant' _              = []

-- Querying

formulae :: [Clause q v t] -> [Formula q v t]
formulae = mapMaybe getForm
  where
    getForm (Clause _ _ f) = Just f
    getForm _              = Nothing

ptrsUsed :: forall q v t . (Ord v,Ord t) => [Clause q v t] -> [(v,t)]
ptrsUsed cl = nubSorted [ (p,t) | Ptr p t :: Term q v t <- universeBi cl ]

appsUsed :: forall q v t . Ord t => [Clause q v t] -> [t]
appsUsed cl = nubSorted [ t | App t _ _ :: Term q v t <- universeBi cl ]

bottomsUsed :: forall q v t . Ord t => [Clause q v t] -> [t]
bottomsUsed cl = nubSorted [ t | Bottom t :: Term q v t <- universeBi cl ]

totalsUsed :: forall q v t . Ord t => [Clause q v t] -> [t]
totalsUsed cl = nubSorted [ t | Total t _ :: Formula q v t <- universeBi cl ]

funsUsed :: forall q v t . Ord v => [Clause q v t] -> [v]
funsUsed cl = nubSorted [ v | Fun v _ :: Term q v t <- universeBi cl ]

ctorsUsed :: forall q v t . Ord v => [Clause q v t] -> [v]
ctorsUsed cl = nubSorted $ [ v | Ctor v _ :: Term q v t <- universeBi cl ]
                        ++ [ v | Proj _ v _ :: Term q v t <- universeBi cl ]

tysUsed :: forall q v t . Ord t => [Clause q v t] -> [t]
tysUsed cl = nubSorted $ concat $
                [ map snd qs | Forall qs _ :: Formula q v t <- universeBi cl ]
             ++ [ map snd qs | Exists qs _ :: Formula q v t <- universeBi cl ]

