-- The implementation of these integers correspond to those in the
-- Agda standard library, which is proved to be a commutative ring
{-# LANGUAGE DeriveDataTypeable, TypeFamilies, CPP #-}
module Main where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),return,undefined)
import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Data.Typeable

(=:=) = (=:=)
type Prop a = a

data Nat = Z | S Nat deriving (Eq,Show,Typeable,Ord)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,15)

data Integ = P Nat | N Nat deriving (Show,Eq,Typeable,Ord)

instance Arbitrary Integ where
  arbitrary = oneof [P `fmap` arbitrary,N `fmap` arbitrary]

-- eqnat Z Z = True
-- eqnat (S m) (S n) = True
-- eqnat _ _ = False
--
-- (==) :: Integ -> Integ -> Bool
-- N x == N y = eqnat x y
-- P x == P y = eqnat x y
-- _   == _   = False

neg :: Integ -> Integ
neg (P (S n)) = N n
neg (P Z)     = P Z
neg (N n)     = P (S n)

prop_neg_involutive :: Integ -> Prop Integ
prop_neg_involutive x = x =:= neg (neg x)

-- Natural addition
x +. Z     = x
x +. (S y) = S (x +. y)

-- Natural multiplication
x *. Z     = Z
x *. (S y) = (x *. y) +. x

-- Natural subtraction
m   -. Z   = P m
Z   -. S n = N n
S m -. S n = m -. n

-- Integer addition
N m + N n = N (S (m +. n))
N m + P n = n -. S m
P m + N n = m -. S n
P m + P n = P (m +. n)

zero = P Z

prop_add_ident_left :: Integ -> Prop Integ
prop_add_ident_left x = x =:= zero + x

prop_add_ident_right :: Integ -> Prop Integ
prop_add_ident_right x = x =:= x + zero

prop_add_assoc :: Integ -> Integ -> Integ -> Prop Integ
prop_add_assoc x y z = (x + (y + z)) =:= ((x + y) + z)

prop_add_comm :: Integ -> Integ -> Prop Integ
prop_add_comm x y = (x + y) =:= (y + x)

prop_add_inv_left :: Integ -> Prop Integ
prop_add_inv_left x = neg x + x =:= zero

prop_add_inv_right :: Integ -> Prop Integ
prop_add_inv_right x = x + neg x =:= zero

-- Integer subtraction
N m - N n = n -. m
N m - P n = N (n +. m)
P m - N n = P (S (n +. m))
P m - P n = m -. n

abs (P n) = n
abs (N n) = S n

data Sign = Pos | Neg deriving (Eq,Show,Ord,Typeable)

instance Arbitrary Sign where
  arbitrary = elements [Pos,Neg]

opposite Pos = Neg
opposite Neg = Pos

Pos *% x = x
Neg *% x = opposite x

prop_sign_assoc :: Sign -> Sign -> Sign -> Prop Sign
prop_sign_assoc s t u = (s *% (t *% u)) =:= ((s *% t) *% u)

prop_sign_ident_left :: Sign -> Prop Sign
prop_sign_ident_left s = s *% Pos =:= s

prop_sign_ident_right :: Sign -> Prop Sign
prop_sign_ident_right s = Pos *% s =:= s

prop_sign_opposite_involutive :: Sign -> Prop Sign
prop_sign_opposite_involutive s = opposite (opposite s) =:= s

prop_sign_triple :: Sign -> Prop Sign
prop_sign_triple s = s *% (s *% s) =:= s

sign :: Integ -> Sign
sign (P _) = Pos
sign (N _) = Neg

_   <| Z     = P Z
Pos <| n     = P n
Neg <| (S m) = N m

i * j = (sign i *% sign j) <| (abs i *. abs j)

one = P (S Z)

prop_mul_ident_left :: Integ -> Prop Integ
prop_mul_ident_left x = x =:= one * x

prop_mul_ident_right :: Integ -> Prop Integ
prop_mul_ident_right x = x =:= x * one

prop_mul_assoc :: Integ -> Integ -> Integ -> Prop Integ
prop_mul_assoc x y z = (x * (y * z)) =:= ((x * y) * z)

prop_mul_comm :: Integ -> Integ -> Prop Integ
prop_mul_comm x y = (x * y) =:= (y * x)

prop_left_distrib :: Integ -> Integ -> Integ -> Prop Integ
prop_left_distrib x y z = x * (y + z) =:= (x * y) + (x * z)

prop_right_distrib :: Integ -> Integ -> Integ -> Prop Integ
prop_right_distrib x y z = (x + y) * z =:= (x * z) + (y * z)

main = hipSpec "Integers.hs" conf 3
  where conf = describe "Integers"
               [ var "x" natType
               , var "y" natType
               , var "z" natType
               , var "i" intType
               , var "j" intType
               , var "k" intType
               , var "s" signType
               , var "t" signType
               , var "u" signType
               , con "P" P
               , con "N" N
               , con "Pos" Pos
               , con "Neg" Neg
               , con "Z" Z
               , con "S" S
               , con "zero" zero
               , con "one"  one
               , con "<|" (<|)
               , con "+" (+)
               , con "-" (-)
               , con "*" (*)
               , con "+." (+.)
               , con "-." (-.)
               , con "*." (*.)
               , con "*%" (*%)
               , con "opposite" opposite
               , con "neg" neg
               , con "abs" abs
               , con "sign" sign
               ]
           where
             natType = (undefined :: Nat)
             intType = (undefined :: Integ)
             signType = (undefined :: Sign)

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return


instance Classify Sign where
  type Value Sign = Sign
  evaluate = return

instance Classify Integ where
  type Value Integ = Integ
  evaluate = return


