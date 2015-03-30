{-# LANGUAGE DeriveDataTypeable #-}
module CFG42 where

import Prelude hiding ((++),show)
import Control.Monad
import Test.QuickCheck hiding ((==>))
import Data.Typeable
import Tip.DSL

data E = T :+: T | T T
  deriving (Typeable,Eq,Ord,Show)

data T = Par E | TX | TY
  deriving (Typeable,Eq,Ord,Show)

data Tok = C | D | X | Y | P
  deriving (Typeable,Eq,Ord,Show)

show :: E -> [Tok]
show (a :+: b) = showTerm a ++ [P] ++ showTerm b
show (T a)     = showTerm a

showTerm :: T -> [Tok]
showTerm (Par e) = [C] ++ show e ++ [D]
showTerm TX      = [X]
showTerm TY      = [Y]

unambig u v = show u =:= show v ==> u =:= v

lemmaTerm v w s t = showTerm v ++ s =:= showTerm w ++ t ==> (v,s) =:= (w,t)

instance Arbitrary E where
  arbitrary = sized arbE

instance Arbitrary T where
  arbitrary = sized arbT

arbE s = frequency
    [ (1,liftM  T     (arbT (s-1)))
    , (s,liftM2 (:+:) (arbT s2) (arbT s2))
    ]
   where
    s2 = s `div` 2

arbT s = frequency
    [ (1,return TX)
    , (1,return TY)
    , (s,liftM Par (arbE (s-1)))
    ]

instance Arbitrary Tok where
  arbitrary = elements [C,D,X,Y,P]

-- injR u v w = v ++ u =:= w ++ u ==> v =:= w
-- inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w
-- injL u v w = u ++ v =:= u ++ w ==> v =:= w

-- unambigTerm u v = showTerm u =:= showTerm v ==> u =:= v

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys
