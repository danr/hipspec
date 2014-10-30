{-# LANGUAGE DeriveDataTypeable #-}
module Class where

import HipSpec
import Nat hiding ((<))

refl :: Nat -> Prop Bool
refl x  = x == x =:= True

sym :: Nat -> Nat -> Prop Bool
sym x y = x == y =:= True ==> y == x =:= True

trans_eq :: Nat -> Nat -> Nat -> Prop Bool
trans_eq x y z = x == y =:= True ==> y == z =:= True ==> x == z =:= True

antisym :: Nat -> Nat -> Prop Bool
antisym x y = x <= y =:= True ==> y <= x =:= True ==> x == y =:= True

asym :: Nat -> Nat -> Prop Bool
asym x y = x < y =:= True ==> y < x =:= False

refl_le :: Nat -> Prop Bool
refl_le x  = x <= x =:= True

irrefl :: Nat -> Prop Bool
irrefl x = x < x =:= False

trans_lt :: Nat -> Nat -> Nat -> Prop Bool
trans_lt x y z = x < y =:= True ==> y < z =:= True ==> x < z =:= True

trans_le :: Nat -> Nat -> Nat -> Prop Bool
trans_le x y z = x <= y =:= True ==> y <= z =:= True ==> x <= z =:= True

