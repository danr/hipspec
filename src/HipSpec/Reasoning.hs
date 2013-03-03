{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}
module HipSpec.Reasoning where

import Test.QuickSpec.Signature
import Test.QuickSpec.Term hiding (depth)
import qualified Test.QuickSpec.Term as T

import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as NER
import qualified Test.QuickSpec.Reasoning.PartialEquationalReasoning as PER
import Test.QuickSpec.Reasoning.PartialEquationalReasoning
    (PEquation(..))

import qualified Test.QuickSpec.Equation as Equation
import Test.QuickSpec.Equation (Equation(..))

import Control.Monad
import Control.Monad.Identity

import Data.List
import Data.Ord
import Data.Tuple
import Data.Function

import Data.Void

class
    (Ord eq,Monad cc) => EQR eq ctx cc
    | eq -> cc ctx
    , cc -> eq ctx
    , ctx -> eq cc
  where
    runEQR :: ctx -> cc a -> (a, ctx)

    evalEQR :: ctx -> cc a -> a
    evalEQR ctx m = fst (runEQR ctx m)

    execEQR :: ctx -> cc a -> ctx
    execEQR ctx m = snd (runEQR ctx m)

    unify :: eq -> cc Bool

    equal :: eq -> cc Bool

    showEquation :: Sig -> eq -> String

    isoDiscard :: eq -> eq -> Bool

--    fromEquation :: Equation -> eq

data NoCC eq = NoCC

instance EQR Void (NoCC Void) Identity where
    runEQR NoCC m = (runIdentity m,NoCC)

    unify _ = return False

    equal _ = return False

    isoDiscard _ _ = False

    showEquation _ eq = show eq

  --  fromEquation _ = ()

instance EQR PEquation PER.Context PER.PEQ where
    runEQR = PER.runPEQ

    unify = PER.unify

    equal = PER.equal

    showEquation = PER.showPEquation

    isoDiscard (pre1 :\/: eq1) (pre2 :\/: eq2)
        = eq1 `isomorphicTo` eq2 && pre1 `isSubsetOf` pre2
      where
        a `isSubsetOf` b = null (a \\ b)

  --  fromEquation eq = [] :\/: eq

instance EQR Equation NER.Context NER.EQ where
    runEQR = NER.runEQ

    unify = NER.unify

    equal = NER.equal

    showEquation = Equation.showEquation

    isoDiscard = isomorphicTo

--     fromEquation = id

-- Renaming
isomorphicTo :: Equation -> Equation -> Bool
e1 `isomorphicTo` e2 =
  case matchEqSkeleton e1 e2 of
    Nothing -> False
    Just xs -> function xs && function (map swap xs)
  where
    matchEqSkeleton :: Equation -> Equation -> Maybe [(Symbol, Symbol)]
    matchEqSkeleton (t :=: u) (t' :=: u') =
      liftM2 (++) (matchSkeleton t t') (matchSkeleton u u')

    matchSkeleton :: Term -> Term -> Maybe [(Symbol, Symbol)]
    matchSkeleton (T.Const f) (T.Const g) | f == g = return []
    matchSkeleton (T.Var x) (T.Var y) = return [(x, y)]
    matchSkeleton (T.App t u) (T.App t' u') =
      liftM2 (++) (matchSkeleton t t') (matchSkeleton u u')
    matchSkeleton _ _ = Nothing

    -- Relation is a function
    function :: (Ord a, Eq b) => [(a, b)] -> Bool
    function
        = all singleton
        . groupBy ((==) `on` fst)
        . nub
        . sortBy (comparing fst)
      where singleton xs = length xs == 1

