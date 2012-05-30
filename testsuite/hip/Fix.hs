module Fix where

import HipPrelude
import Prelude (fmap,(!!),Eq,Show,Bool(..),(.),iterate)

data Nat = S Nat | Z deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary = sized (fmap (nats !!) . choose . (,) 0)
    where nats = iterate S Z

not True = False
not False = True

even :: Nat -> Bool
even Z     = True
even (S x) = odd x

odd :: Nat -> Bool
odd Z     = False
odd (S x) = even x

evenFixMe :: (Nat -> Bool) -> (Nat -> Bool) -> Nat -> Bool
evenFixMe evenUnRec oddUnRec Z     = True
evenFixMe evenUnRec oddUnRec (S x) = oddUnRec x

oddFixMe :: (Nat -> Bool) -> (Nat -> Bool) -> Nat -> Bool
oddFixMe evenUnRec oddUnRec Z     = False
oddFixMe evenUnRec oddUnRec (S x) = evenUnRec x

fst (x,y) = x
snd (x,y) = y

uncurry f t = f (fst t) (snd t)

fix f = f (fix f)

evenFix,oddFix :: Nat -> Bool
fixed = fix (\t -> (uncurry evenFixMe t,uncurry oddFixMe t))
evenFix = fst fixed
oddFix  = snd fixed

prop_even,prop_odd :: Nat -> Prop Bool
prop_even x = even x =:= evenFix x
prop_odd  x = odd x  =:= oddFix x

prop_even_not_odd :: Nat -> Prop Bool
prop_even_not_odd x = even x =:= not (odd x)

prop_odd_not_even :: Nat -> Prop Bool
prop_odd_not_even x = odd x =:= not (even x)

prop_odd_even_incr :: Nat -> Prop Bool
prop_odd_even_incr x = odd x =:= even (S x)

-- Single fix -----------------------------------------------------------------
evenSinglFixMe :: (Nat -> Bool) -> Nat -> Bool
evenSinglFixMe evenUnRec Z     = True
evenSinglFixMe evenUnRec (S x) = oddWhere x
  where
    oddWhere Z     = False
    oddWhere (S x) = evenUnRec x

evenSingl :: Nat -> Bool
evenSingl = fix evenSinglFixMe

prop_evenSingl :: Nat -> Prop Bool
prop_evenSingl x = evenSingl x =:= even x

prop_evenSinglFix :: Nat -> Prop Bool
prop_evenSinglFix x = evenSingl x =:= evenFix x
