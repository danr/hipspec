-- Properties of Natural numbers
-- Many of these examples come from Zeno
module Nat where

import HipPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..))

data Nat = Z | S Nat

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

Z     * _ = Z
(S x) * y = y + (x * y)

min Z     _     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max Z     y     = y
max x     Z     = x
max (S x) (S y) = S (max x y)

--prop_zero_is_one :: Prop Nat
--prop_zero_is_one = Z =/= S Z

prop_stuff :: Prop Nat
prop_stuff = S Z * S (S Z) =:= S (S (S Z)) - S Z

prop_refl :: Nat -> Prop Bool
prop_refl x = proveBool (x == x)

prop_movesuc :: Nat -> Nat -> Prop Nat
prop_movesuc x y = S x + y =:= x + S y

prop_assoc_plus :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_plus x y z = x + (y + z) =:= (x + y) + z

prop_assoc_mul :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_mul x y z = x * (y * z) =:= (x * y) * z

prop_right_identity_plus :: Nat -> Prop Nat
prop_right_identity_plus x = x + Z =:= x

prop_left_identity_plus :: Nat -> Prop Nat
prop_left_identity_plus x = Z + x =:= x

prop_right_identity_mul :: Nat -> Prop Nat
prop_right_identity_mul x = x * S Z =:= x

prop_left_identity_mul :: Nat -> Prop Nat
prop_left_identity_mul x = S Z * x =:= x

prop_add_comm :: Nat -> Nat -> Prop Nat
prop_add_comm x y = x + y =:= y + x

prop_mul_lemma :: Nat -> Nat -> Prop Nat
prop_mul_lemma m n = m * S n =:= m + m * n

prop_mul_comm :: Nat -> Nat -> Prop Nat
prop_mul_comm x y = x * y =:= y * x

prop_left_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_left_distrib x y z = x * (y + z) =:= (x * y) + (x * z)

prop_right_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_right_distrib x y z = (x + y) * z =:= (x * z) + (y * z)

prop_min_absorb :: Nat -> Nat -> Prop Nat
prop_min_absorb x y = min x (max x y) =:= x

prop_max_absorb :: Nat -> Nat -> Prop Nat
prop_max_absorb x y = max x (min x y) =:= x

--prop_idem_plus :: Nat -> Prop Nat
--prop_idem_plus x = x + x =/= x
--
--prop_idem_mul :: Nat -> Prop Nat
--prop_idem_mul x = x * x =/= x

prop_minus_zeroish :: Nat -> Nat -> Prop Nat
prop_minus_zeroish n m = n - (n + m) =:= Z

prop_minus_absorbish  :: Nat -> Nat -> Prop Nat
prop_minus_absorbish n m = (n + m) - n =:= m

prop_minus_distribish :: Nat -> Nat -> Nat -> Prop Nat
prop_minus_distribish k m n = (k + m) - (k + n) =:= m - n

prop_minus_assocish :: Nat -> Nat -> Nat -> Prop Nat
prop_minus_assocish i j k = (i - j) - k =:= i - (j + k)

prop_minus_zero :: Nat -> Prop Nat
prop_minus_zero m = m - m =:= Z

prop_lt_zero_eq_zero :: Nat -> Prop Bool
prop_lt_zero_eq_zero n = n <= Z =:= n == Z

prop_le_succ_plus :: Nat -> Nat -> Prop Bool
prop_le_succ_plus i m = proveBool (i < S (i + m))

prop_le_plus :: Nat -> Nat -> Prop Bool
prop_le_plus n m = proveBool (n <= (n + m))

prop_le_plus_sym :: Nat -> Nat -> Prop Bool
prop_le_plus_sym n m = proveBool (n <= (m + n))

prop_max_assoc :: Nat -> Nat -> Nat -> Prop Nat
prop_max_assoc a b c = max (max a b) c =:= max a (max b c)

prop_max_sym :: Nat -> Nat -> Prop Nat
prop_max_sym a b = max a b =:= max b a

prop_max_le :: Nat -> Nat -> Prop Bool
prop_max_le a b = (max a b) == a =:= b <= a

prop_max_le_sym :: Nat -> Nat -> Prop Bool
prop_max_le_sym a b = (max a b) == b =:= a <= b

prop_min_assoc :: Nat -> Nat -> Nat -> Prop Nat
prop_min_assoc a b c = min (min a b) c =:= min a (min b c)

prop_min_sym :: Nat -> Nat -> Prop Nat
prop_min_sym a b = min a b =:= min b a

prop_min_le :: Nat -> Nat -> Prop Bool
prop_min_le a b = min a b == a =:= a <= b

prop_min_le_sym :: Nat -> Nat -> Prop Bool
prop_min_le_sym a b = min a b == b =:= b <= a

prop_minus_plus :: Nat -> Nat -> Prop Nat
prop_minus_plus n m = (m + n) - n =:= m

prop_lt_suc  :: Nat -> Nat -> Prop Bool
prop_lt_suc i m = proveBool (i < S (m + i))

prop_succ_minus_3 :: Nat -> Nat -> Nat -> Prop Nat
prop_succ_minus_3 m n k = (S m - n) - S k =:= (m - n) - k

