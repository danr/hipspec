{-# LANGUAGE DeriveDataTypeable #-}
module Ordinals where

import HipSpec
import qualified Prelude as P

data Nat = Z | S Nat deriving (P.Show,Typeable)

Z   `plus` y = y
S x `plus` y = S (x `plus` y)

Z   `mul` y = Z
S x `mul` y = y `plus` (x `mul` y)

data Ord = Zero | Suc Ord | Lim (Nat -> Ord)
 deriving (Typeable)

Zero  `oplus` y = y
Suc x `oplus` y = Suc (x `oplus` y)
Lim f `oplus` y = Lim (\ n -> f n `oplus` y)

prop_assoc_plus x y z = x `plus` (y `plus` z) =:= (x `plus` y) `plus` z

prop_assoc_oplus x y z = x `oplus` (y `oplus` z) =:= (x `oplus` y) `oplus` z

prop_assoc_mul x y z = x `mul` (y `mul` z) =:= (x `mul` y) `mul` z
prop_plus_right x = x `plus` Z =:= x

prop_mul_right x = x `mul` Z =:= Z
