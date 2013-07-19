{-# LANGUAGE DeriveDataTypeable #-}
module List where

import Prelude hiding ((++),length,(+))
import qualified Prelude
import HipSpec

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

sig = [ vars ["m", "n", "o"]    (undefined :: Nat)
      , vars ["x", "y", "z"]    (undefined :: A)
      , vars ["xs", "ys", "zs"] (undefined :: [A])
      , fun0 "Z"                Z
      , fun1 "S"                S
      , fun2 "+"                (+)

      , fun0 "[]"               ([] :: [A])
      , fun2 ":"                ((:) :: A -> [A] -> [A])
      , fun2 "++"               ((++) :: [A] -> [A] -> [A])
      , fun1 "length"           (length :: [A] -> Nat)

-- One more time!!
      , fun0 "[]"               ([] :: [[A]])
      , fun2 ":"                ((:) :: [A] -> [[A]] -> [[A]])
      , fun2 "++"               ((++) :: [[A]] -> [[A]] -> [[A]])
      , fun1 "length"           (length :: [[A]] -> Nat)

      , fun2 "(,)"              ((,) :: A -> A -> (A,A))
      , fun0 "True" True
      , fun0 "LT" LT
      , fun0 "()" ()
      ]

data Nat = Z | S Nat deriving (Eq,Ord,Show,Typeable)

infixl 6 +

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \ s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)

