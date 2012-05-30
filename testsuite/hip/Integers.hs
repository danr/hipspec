-- The implementation of these integers correspond to those in the
-- Agda standard library, which is proved to be a commutative ring
module Integers where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..))

data Nat = Z | S Nat deriving (Eq)

-- instance Arbitrary Nat where
--   arbitrary =
--     let nats = iterate S Z
--     in  (nats !!) `fmap` choose (0,50)

data Integ = P Nat | N Nat deriving (Eq)

-- instance Arbitrary Integ where
--   arbitrary = oneof [P `fmap` arbitrary,N `fmap` arbitrary]

eqnat Z Z = True
eqnat (S m) (S n) = True
eqnat _ _ = False

(==) :: Integ -> Integ -> Bool
N x == N y = eqnat x y
P x == P y = eqnat x y
_   == _   = False

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
N m +! N n = N (S (m +. n))
N m +! P n = n -. S m
P m +! N n = m -. S n
P m +! P n = P (m +. n)

zero = P Z

prop_add_ident_left :: Integ -> Prop Integ
prop_add_ident_left x = x =:= zero +! x

prop_add_ident_right :: Integ -> Prop Integ
prop_add_ident_right x = x =:= x +! zero

prop_add_assoc :: Integ -> Integ -> Integ -> Prop Integ
prop_add_assoc x y z = (x +! (y +! z)) =:= ((x +! y) +! z)

prop_add_comm :: Integ -> Integ -> Prop Integ
prop_add_comm x y = (x +! y) =:= (y +! x)

prop_add_inv_left :: Integ -> Prop Integ
prop_add_inv_left x = neg x +! x =:= zero

prop_add_inv_right :: Integ -> Prop Integ
prop_add_inv_right x = x +! neg x =:= zero

-- Integer subtraction
N m -! N n = n -. m
N m -! P n = N (n +. m)
P m -! N n = P (S (n +. m))
P m -! P n = m -. n

abs' (P n) = n
abs' (N n) = S n

data Sign = Pos | Neg deriving (Eq)

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

i *! j = (sign i *% sign j) <| (abs' i *. abs' j)

one = P (S Z)

prop_mul_ident_left :: Integ -> Prop Integ
prop_mul_ident_left x = x =:= one *! x

prop_mul_ident_right :: Integ -> Prop Integ
prop_mul_ident_right x = x =:= x *! one

prop_mul_assoc :: Integ -> Integ -> Integ -> Prop Integ
prop_mul_assoc x y z = (x *! (y *! z)) =:= ((x *! y) *! z)

prop_mul_comm :: Integ -> Integ -> Prop Integ
prop_mul_comm x y = (x *! y) =:= (y *! x)

prop_left_distrib :: Integ -> Integ -> Integ -> Prop Integ
prop_left_distrib x y z = x *! (y +! z) =:= (x *! y) +! (x *! z)

prop_right_distrib :: Integ -> Integ -> Integ -> Prop Integ
prop_right_distrib x y z = (x +! y) *! z =:= (x *! z) +! (y *! z)

{-
main = do
  quickCheck (printTestCase "prop_neg_involutive" prop_neg_involutive)
  quickCheck (printTestCase "prop_add_ident_left" prop_add_ident_left)
  quickCheck (printTestCase "prop_add_ident_right" prop_add_ident_right)
  quickCheck (printTestCase "prop_add_assoc" prop_add_assoc)
  quickCheck (printTestCase "prop_add_comm" prop_add_comm)
  quickCheck (printTestCase "prop_add_inv_left" prop_add_inv_left)
  quickCheck (printTestCase "prop_add_inv_right" prop_add_inv_right)
  quickCheck (printTestCase "prop_sign_assoc" prop_sign_assoc)
  quickCheck (printTestCase "prop_sign_ident_left" prop_sign_ident_left)
  quickCheck (printTestCase "prop_sign_opposite_involutive" prop_sign_opposite_involutive)
  quickCheck (printTestCase "prop_sign_triple" prop_sign_triple)
  quickCheck (printTestCase "prop_mul_ident_left" prop_mul_ident_left)
  quickCheck (printTestCase "prop_mul_ident_right" prop_mul_ident_right)
  quickCheck (printTestCase "prop_mul_assoc" prop_mul_assoc)
  quickCheck (printTestCase "prop_mul_comm" prop_mul_comm)

-}
