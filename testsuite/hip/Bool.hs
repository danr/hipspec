module Main where

import Hip.Prelude
import Hip.HipSpec
import Prelude (Bool(..))

True  && a = a
False && _ = False

False || a = a
True  || _ = True

not True  = False
not False = True

prop_and_comm :: Bool -> Bool -> Prop Bool
prop_and_comm x y = y && x =:= x && y

prop_or_comm :: Bool -> Bool -> Prop Bool
prop_or_comm x y = y || x =:= x || y

prop_and_idem :: Bool -> Prop Bool
prop_and_idem x = x && x =:= x

prop_or_idem :: Bool -> Prop Bool
prop_or_idem x = x || x =:= x

prop_and_identity :: Bool -> Prop Bool
prop_and_identity x = x && True =:= x

prop_and_zero :: Bool -> Prop Bool
prop_and_zero x = x && False =:= False

prop_or_zero :: Bool -> Prop Bool
prop_or_zero x = x || True =:= True

prop_or_identity :: Bool -> Prop Bool
prop_or_identity x = x || False =:= x

prop_not_true :: Prop Bool
prop_not_true = not True =:= False

prop_not_false :: Prop Bool
prop_not_false = not False =:= True

prop_and_assoc :: Bool -> Bool -> Bool -> Prop Bool
prop_and_assoc x y z = x && (y && z) =:= (x && y) && z

prop_or_assoc :: Bool -> Bool -> Bool -> Prop Bool
prop_or_assoc x y z = x || (y || z) =:= (x || y) || z

prop_and_assoc_comm :: Bool -> Bool -> Bool -> Prop Bool
prop_and_assoc_comm x y z = y && (x && z) =:= x && (y && z)

prop_or_assoc_comm :: Bool -> Bool -> Bool -> Prop Bool
prop_or_assoc_comm x y z = y || (x || z) =:= x || (y || z)

prop_and_absorb :: Bool -> Bool -> Prop Bool
prop_and_absorb x y = x && (x || y) =:= x

prop_or_absorb :: Bool -> Bool -> Prop Bool
prop_or_absorb x y = x || (x && y) =:= x

prop_not_involutive :: Bool -> Prop Bool
prop_not_involutive x = not (not x) =:= x

prop_and_complement :: Bool -> Prop Bool
prop_and_complement x = x && not x =:= False

prop_or_complement :: Bool -> Prop Bool
prop_or_complement x = x || not x =:= True

prop_and_distrib :: Bool -> Bool -> Bool -> Prop Bool
prop_and_distrib x y z = (x || y) && (x || z) =:= x || (y && z)

prop_or_distrib :: Bool -> Bool -> Bool -> Prop Bool
prop_or_distrib x y z = (x && y) || (x && z) =:= x && (y || z)

prop_de_morgan_0 :: Bool -> Bool -> Prop Bool
prop_de_morgan_0 x y = not x && not y =:= not (x || y)

prop_de_morgan_1 :: Bool -> Bool -> Prop Bool
prop_de_morgan_1 x y = not x || not y =:= not (x && y)

main = hipSpec "Bool.hs" [fun0 "True" True]
