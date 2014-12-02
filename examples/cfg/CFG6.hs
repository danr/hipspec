{-# LANGUAGE DeriveDataTypeable #-}
module CFG6 where

import Prelude hiding ((++),(+))
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

(+++) :: [a] -> [a] -> [a]
(x:xs) +++ ys = x:(xs +++ ys)
[]     +++ ys = ys

data S = A A | B B deriving (Typeable,Eq,Ord,Show)

data A = SA A | ZA deriving (Typeable,Eq,Ord,Show)

data B = SB B | ZB deriving (Typeable,Eq,Ord,Show)

data Tok = X | Y | Z
  deriving (Typeable,Eq,Ord,Show)

data Nat = S Nat | Zero deriving (Eq,Show,Typeable,Ord)

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

linS :: S -> [Tok]
linS (A a) = linA a
linS (B b) = linB b

linA :: A -> [Tok]
linA ZA     = [X,Z,Y]
linA (SA a) = [X] +++ linA a +++ [Y]

linB :: B -> [Tok]
linB ZB     = [X,Z,Y,Y]
linB (SB b) = [X] +++ linB b +++ [Y,Y]

-- this one is false:
alemmaS_L v w s t = linS v +++ s =:= linS w +++ t ==> (v,s) =:= (w,t)

unambigS u v = linS u =:= linS v ==> u =:= v
unambigA u v = linA u =:= linA v ==> u =:= v
unambigB u v = linB u =:= linB v ==> u =:= v

injR u v w = v +++ u =:= w +++ u ==> v =:= w
inj1 x v w = v +++ [x] =:= w +++ [x] ==> v =:= w
injL u v w = u +++ v =:= u +++ w ==> v =:= w

lemmaA_L v w s t = linA v +++ s =:= linA w +++ t ==> (v,s) =:= (w,t)
lemmaB_L v w s t = linB v +++ s =:= linB w +++ t ==> (v,s) =:= (w,t)

{-
lemmaAB a b = linA a =:= linB b ==> A a =:= B b {- i.e: false -}

lemmaCountA a = count X (linA a) =:= count Y (linA a)
lemmaCountB b = double (count X (linB b)) =:= count Y (linB b)

countMorph x xs ys = count x (xs +++ ys) =:= count x xs + count x ys

nonZeroA x a = nonZero (count x (linA a)) =:= True
nonZeroB x b = nonZero (count x (linB b)) =:= True
-}

-- after either of these (because commutativity), all the lemmas about double below follow
plusInjL x y z = y + x =:= z + x ==> y =:= z
plusInjR x y z = x + y =:= x + z ==> y =:= z

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

