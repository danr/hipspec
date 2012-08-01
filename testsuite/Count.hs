{-# LANGUAGE DeriveDataTypeable #-}
{-

    count n (rev xs) = count n xs,

    from "Productive Use of Failure in Inductive Proof"

    Use --indvars=3 to get rid of lots of boring proofs

-}
module Main where

import Prelude (Bool(..),error,toEnum,fromEnum,pred,succ,sqrt,round
               ,Enum,Eq,Ord,Show,return,(.),undefined)

import Data.Typeable

import Hip.Prelude
import Hip.HipSpec

main = hipSpec "Count.hs" conf
  where
    conf = [ vars ["x","y","z"]    elemType
           , vars ["xs","ys","zs"] listType
           , fun0 "[]"             ([]    :: [Nat])
           , fun2 ":"              ((:)   :: Nat  -> [Nat] -> [Nat])
           , fun2 "++"             ((++)  :: [Nat] -> [Nat] -> [Nat])
           , fun2 "count"          (count :: Nat -> [Nat] -> Nat)
           , fun1 "rev"            (rev   :: [Nat] -> [Nat])
           , fun2 "=="             (==)
           , fun0 "True"           True
           , fun0 "Z"              Z
           , fun1 "S"              S
           , fun2 "+"              (+)
           ]
    elemType  = (error "Elem type" :: Nat)
    listType = (error "List type" :: [Nat])

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized (\s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x))

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

-- Boolean functions

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- Natural numbers

Z     == Z     = True
(S x) == (S y) = x == y
_     == _     = False

Z     <= _     = True
(S x) <= (S y) = x <= y
_     <= _     = False

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

-- List functions

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _    -> count x ys

prop_52 :: Nat -> [Nat] -> Prop Nat
prop_52 n xs = (count n xs =:= count n (rev xs))

