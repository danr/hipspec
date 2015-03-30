{-# LANGUAGE DeriveDataTypeable #-}
module CFG where

import Prelude hiding ((++),show)
import Control.Monad
import Test.QuickCheck hiding ((==>))
import Data.Typeable
import Tip.DSL

data E = E :+: E | EX | EY
  deriving (Typeable,Eq,Ord,Show)

data Tok = C | D | X | Y | P
  deriving (Typeable,Eq,Ord,Show)

show :: E -> [Tok]
show (a :+: b) = [C] ++ show a ++ [P] ++ show b ++ [D]
show EX        = [X]
show EY        = [Y]

unambig u v = show u =:= show v ==> u =:= v

lemma :: E -> E -> [Tok] -> [Tok] -> Prop (E,[Tok])
lemma v w s t = show v ++ s =:= show w ++ t ==> (v,s) =:= (w,t)
















































{-
lemma v w s t = show v ++ s =:= show w ++ t ==> (v,s) =:= (w,t)
-}

instance Arbitrary E where
  arbitrary = sized arb
   where
    arb s = frequency
      [ (1,return EX)
      , (1,return EY)
      , (s,liftM2 (:+:) (arb s2) (arb s2))
      ]
     where
      s2 = s `div` 2

instance Arbitrary Tok where
  arbitrary = elements [C,D,X,Y,P]

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

