{-# LANGUAGE DeriveDataTypeable #-}
module CFG6 where

import Prelude hiding ((++))
import Control.Monad
import HipSpec hiding (A,B)

{-

From packrat parsing icfp 2002:

S <- A | B
A <- xAy | xzy
B <- xByy | xzyy

The way we show that this is unambiguous is to show that:

count x A = count y A
double (count x B) = count y B
count x A > 0
count y A > 0
count x B > 0
count y B > 0
double x != x for x > x, using:
  x + y = x + z => y = z
  double x = x + x
  (and perhaps also commutativity)
list homomorphism of count x and +

-}

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

data S = A A | B B deriving (Typeable,Eq,Ord,Show)

data A = SA A | ZA deriving (Typeable,Eq,Ord,Show)

data B = SB B | ZB deriving (Typeable,Eq,Ord,Show)

count :: Char -> [Char] -> Integer
count t (x:xs) | t == x    = 1 + count t xs
               | otherwise = count t xs
count t [] = 0

linS :: S -> [Char]
linS (A a) = linA a
linS (B b) = linB b

linA :: A -> [Char]
linA ZA     = "xzy"
linA (SA a) = "x" ++ linA a ++ "y"

linB :: B -> [Char]
linB ZB     = "xzyy"
linB (SB b) = "x" ++ linB b ++ "yy"

unambigS u v = linS u =:= linS v ==> u =:= v
unambigA u v = linA u =:= linA v ==> u =:= v
unambigB u v = linB u =:= linB v ==> u =:= v

injR u v w = v ++ u =:= w ++ u ==> v =:= w
inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w
injL u v w = u ++ v =:= u ++ w ==> v =:= w

lemmaA_L v w s t = linA v ++ s =:= linA w ++ t ==> (v,s) =:= (w,t)
lemmaB_L v w s t = linB v ++ s =:= linB w ++ t ==> (v,s) =:= (w,t)

xx = 'x'
yy = 'y'
zz = 'z'

plus :: Integer -> Integer -> Integer
plus x y = x + y

positive :: Integer -> Bool
positive x = x > 0

{-
lemmaAB a b = linA a =:= linB b ==> A a =:= B b {- i.e: false -}

lemmaCountA a = count X (linA a) =:= count Y (linA a)
lemmaCountB b = double (count X (linB b)) =:= count Y (linB b)

countMorph x xs ys = count x (xs ++ ys) =:= count x xs + count x ys

nonZeroA x a = nonZero (count x (linA a)) =:= True
nonZeroB x b = nonZero (count x (linB b)) =:= True
-}


-- this one is false:
-- lemmaS_L v w s t = linS v ++ s =:= linS w ++ t ==> (v,s) =:= (w,t)

instance Arbitrary S where
  arbitrary = oneof [liftM A arbitrary,liftM B arbitrary]

instance Arbitrary A where
  arbitrary = sized arb
   where
    arb s = frequency
      [ (1,return ZA)
      , (s,liftM SA (arb (s-1)))
      ]

instance Arbitrary B where
  arbitrary = sized arb
   where
    arb s = frequency
      [ (1,return ZB)
      , (s,liftM SB (arb (s-1)))
      ]

