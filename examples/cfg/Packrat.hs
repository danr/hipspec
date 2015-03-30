{-# LANGUAGE DeriveDataTypeable #-}
module Packrat where

import Prelude hiding ((++),(+),show)
import Control.Monad
import Test.QuickCheck hiding ((==>))
import Data.Typeable
import Tip.DSL

data S = A A | B B deriving (Typeable,Eq,Ord,Show)

data A = SA A | ZA deriving (Typeable,Eq,Ord,Show)

data B = SB B | ZB deriving (Typeable,Eq,Ord,Show)

data Tok = X | Y | Z deriving (Typeable,Eq,Ord,Show)

showS :: S -> [Tok]
showS (A a) = showA a
showS (B b) = showB b

showA :: A -> [Tok]
showA ZA     = [X,Z,Y]
showA (SA a) = [X] ++ showA a ++ [Y]

showB :: B -> [Tok]
showB ZB     = [X,Z,Y,Y]
showB (SB b) = [X] ++ showB b ++ [Y,Y]

unambigS u v = showS u =:= showS v ==> u =:= v
unambigA u v = showA u =:= showA v ==> u =:= v
unambigB u v = showB u =:= showB v ==> u =:= v



























{-

injR u v w = v ++ u =:= w ++ u ==> v =:= w
inj1 x v w = v ++ [x] =:= w ++ [x] ==> v =:= w
injL u v w = u ++ v =:= u ++ w ==> v =:= w

-}






{-

plusInjL x y z = y + x =:= z + x ==> y =:= z
plusInjR x y z = x + y =:= x + z ==> y =:= z

-}

(+) :: Nat -> Nat -> Nat
S n  + m = S (n + m)
Zero + m = m

nonZero :: Nat -> Bool
nonZero Zero = False
nonZero _    = True

count :: Tok -> [Tok] -> Nat
count t (x:xs) | t `eqTok` x = S (count t xs)
               | otherwise = count t xs
count t [] = Zero

{-# NOINLINE eqTok #-}
eqTok :: Tok -> Tok -> Bool
eqTok X X = True
eqTok Y Y = True
eqTok Z Z = True
eqTok _ _ = False

double :: Nat -> Nat
double Zero  = Zero
double (S x) = S (S (double x))

-- this one is false:
--alemmaS_L v w s t = showS v ++ s =:= showS w ++ t ==> (v,s) =:= (w,t)

{-

-- lemmaA_L v w s t = showA v ++ s =:= showA w ++ t ==> (v,s) =:= (w,t)
-- lemmaB_L v w s t = showB v ++ s =:= showB w ++ t ==> (v,s) =:= (w,t)

-- lemmaAB a b = showA a =:= showB b ==> A a =:= B b {- i.e: false -}

--lemmaCountA a = count X (showA a) =:= count Y (showA a)
--lemmaCountB b = double (count X (showB b)) =:= count Y (showB b)

-- countMorph x xs ys = count x (xs ++ ys) =:= count x xs + count x ys

--nonZeroA x a = nonZero (count x (showA a)) =:= True
--nonZeroB x b = nonZero (count x (showB b)) =:= True

-- after either of these (because commutativity), all the lemmas about double below follow
plusInjL x y z = y + x =:= z + x ==> y =:= z
plusInjR x y z = x + y =:= x + z ==> y =:= z

-}

{-
lemmaDouble x = double (S x) =:= S x ==> x =:= S x
lemmaDouble2 x = double x =:= x ==> x =:= Zero

lemmaPlus x  = S x + S x =:= S x ==> x =:= S x
lemmaPlus2 x = x + x =:= x ==> x =:= Zero
-}



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

instance Arbitrary Tok where
  arbitrary = elements [X,Y,Z]

instance Arbitrary Nat where
    arbitrary =
        let nats = iterate S Zero
        in  (nats !!) `fmap` choose (0,5)


(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

-- hipspec CFG6.hs  --extra-trans=double,count,nonZero --z3 --vampire

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

data Nat = S Nat | Zero deriving (Eq,Show,Typeable,Ord)
