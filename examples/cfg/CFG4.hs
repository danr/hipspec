{-# LANGUAGE DeriveDataTypeable #-}
module CFG4 where

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
show (a :+: b) = showTerm a ++ [P] ++ showTerm b
show EX        = [X]
show EY        = [Y]

showTerm :: E -> [Tok]
showTerm e@(_ :+: _) = [C] ++ show e ++ [D]
showTerm EX          = [X]
showTerm EY          = [Y]

unambig u v = show u =:= show v ==> u =:= v

-- lemma v w s t =
--  show v ++ s =:= show w ++ t ==> (v,s) =:= (w,t)

lemmaTerm v w s t = showTerm v ++ s =:= showTerm w ++ t ==> (v,s) =:= (w,t)

















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

-- injR u v w = v ++ u =:= w ++ u ==> v =:= w
-- inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w
-- injL u v w = u ++ v =:= u ++ w ==> v =:= w

-- unambigTerm u v = showTerm u =:= showTerm v ==> u =:= v

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys
