-- Properties of Natural numbers, with definitions recursive on the
-- second argument
module Nat2ndArg where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..))

data Nat = Z | S Nat
  deriving (Eq,Ord,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,25)

x + Z   = x
x + S y = S (x + y)

_ * Z   = Z
x * S y = x + (x * y)

Z   - _   = Z
x   - Z   = x
S x - S y = x - y

Z   <= _   = True
_   <= Z   = False
S x <= S y = x <= y

_   < Z   = False
Z   < _   = True
S x < S y = x < y

-- Only properties directly or indirectly regarding +

prop_assoc_plus :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_plus x y z
  = x + (y + z) =:= (x + y) + z

prop_assoc_mul :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_mul x y z
  = x * (y * z) =:= (x * y) * z

prop_right_identity_plus :: Nat -> Prop Nat
prop_right_identity_plus x
  = x + Z =:= x

prop_left_identity_plus :: Nat -> Prop Nat
prop_left_identity_plus x
  = Z + x =:= x

prop_right_identity_mul :: Nat -> Prop Nat
prop_right_identity_mul x
  = x * S Z =:= x

prop_left_identity_mul :: Nat -> Prop Nat
prop_left_identity_mul x
  = S Z * x =:= x

prop_add_comm :: Nat -> Nat -> Prop Nat
prop_add_comm x y
  = x + y =:= y + x

prop_mul_comm :: Nat -> Nat -> Prop Nat
prop_mul_comm x y
  = x * y =:= y * x

prop_left_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_left_distrib x y z
  = x * (y + z) =:= (x * y) + (x * z)

prop_right_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_right_distrib x y z
  = (x + y) * z =:= (x * z) + (y * z)

prop_idem_plus :: Nat -> Prop Nat
prop_idem_plus x
  = x + x =/= x

prop_idem_mul :: Nat -> Prop Nat
prop_idem_mul x
  = x * x =/= x

prop_minus_zeroish :: Nat -> Nat -> Prop Nat
prop_minus_zeroish n m
  = n - (n + m) =:= Z

prop_minus_absorbish  :: Nat -> Nat -> Prop Nat
prop_minus_absorbish n m
  = (n + m) - n =:= m

prop_minus_distribish :: Nat -> Nat -> Nat -> Prop Nat
prop_minus_distribish k m n
  = (k + m) - (k + n) =:= m - n

prop_le_succ_plus :: Nat -> Nat -> Prop Bool
prop_le_succ_plus i m
  = proveBool (i < S (i + m))

prop_le_plus :: Nat -> Nat -> Prop Bool
prop_le_plus n m
  = proveBool (n <= (n + m))

prop_le_plus_sym :: Nat -> Nat -> Prop Bool
prop_le_plus_sym n m
  = proveBool (n <= (m + n))

prop_minus_plus :: Nat -> Nat -> Prop Nat
prop_minus_plus n m
  = (m + n) - n =:= m

prop_lt_suc  :: Nat -> Nat -> Prop Bool
prop_lt_suc i m =
  proveBool (i < S (m + i))

main = do
  quickCheck (printTestCase "prop_assoc_plus" prop_assoc_plus)
  quickCheck (printTestCase "prop_assoc_mul" prop_assoc_mul)
  quickCheck (printTestCase "prop_right_identity_plus" prop_right_identity_plus)
  quickCheck (printTestCase "prop_left_identity_plus" prop_left_identity_plus)
  quickCheck (printTestCase "prop_right_identity_mul" prop_right_identity_mul)
  quickCheck (printTestCase "prop_left_identity_mul" prop_left_identity_mul)
  quickCheck (printTestCase "prop_add_comm" prop_add_comm)
  quickCheck (printTestCase "prop_mul_comm" prop_mul_comm)
  quickCheck (printTestCase "prop_left_distrib" prop_left_distrib)
  quickCheck (printTestCase "prop_right_distrib" prop_right_distrib)
  quickCheck (printTestCase "prop_idem_plus" prop_idem_plus)
  quickCheck (printTestCase "prop_idem_mul" prop_idem_mul)
  quickCheck (printTestCase "prop_minus_zeroish" prop_minus_zeroish)
  quickCheck (printTestCase "prop_minus_absorbish" prop_minus_absorbish)
  quickCheck (printTestCase "prop_minus_distribish" prop_minus_distribish)
  quickCheck (printTestCase "prop_le_succ_plus" prop_le_succ_plus)
  quickCheck (printTestCase "prop_le_plus" prop_le_plus)
  quickCheck (printTestCase "prop_le_plus_sym" prop_le_plus_sym)
  quickCheck (printTestCase "prop_minus_plus" prop_minus_plus)
  quickCheck (printTestCase "prop_lt_suc" prop_lt_suc)
