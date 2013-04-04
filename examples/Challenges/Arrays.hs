{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module Arrays where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),return,otherwise,undefined,zip)
import HipSpec.Prelude
import Test.QuickSpec.Signature
import Test.QuickCheck.All
import Data.List (delete)

data Nat = S Nat | Z deriving (Eq,Show,Typeable,Ord)

instance Arbitrary Nat where
    arbitrary = frequency ([5,5,3,2,1] `zip` fmap return nats)
      where nats = iterate S Z
--    in (nats !!) `fmap` choose (0,5)

data Set = NCons Nat Set | NNil
  deriving (Eq,Typeable,Ord,Show)

instance Arbitrary Set where
    arbitrary = toSet `fmap` arbitrary

fromSet :: Set -> [Nat]
fromSet (NCons x xs) = x : fromSet xs
fromSet NNil         = []

toSet :: [Nat] -> Set
toSet (x:xs) = NCons x (toSet xs)
toSet []     = NNil

(<) :: Nat -> Nat -> Bool
Z   < Z   = False
Z   < S _ = True
S _ < Z   = False
S x < S y = x < y

(<=) :: Nat -> Nat -> Bool
Z   <= Z   = True
Z   <= S _ = True
S _ <= Z   = False
S x <= S y = x <= y

(&&) :: Bool -> Bool -> Bool
True && x = x
_    && _ = False


isSet :: Set -> Bool
isSet (NCons x (NCons y xs)) = if x < y then isSet (NCons y xs) else False
isSet (NCons x _) = True
isSet NNil = True

(==) :: Nat -> Nat -> Bool
Z   == Z   = True
Z   == S _ = False
S _ == Z   = False
S x == S y = x == y

add :: Nat -> Set -> Set
add n NNil = NCons n NNil
add n (NCons x xs)
    | n == x    = NCons x xs
    | n <  x    = NCons n (NCons x xs)
    | otherwise = NCons x (add n xs)

del :: Nat -> Set -> Set
del _ NNil         = NNil
del n (NCons x xs)
    | n == x    = xs
    | n < x     = NCons x xs
    | otherwise = NCons x (del n xs)

mkSet :: Set -> Set
mkSet NNil         = NNil
mkSet (NCons x xs) = add x (mkSet xs)

-- prop_koen :: XY -> Set -> Prop Set
-- prop_koen xy xs
--     =   add (getX xy) (del (getY xy) (mkSet xs))
--     =:= del (getY xy) (add (getX xy) (mkSet xs))

data XY = XY Nat Nat
  deriving (Eq,Ord,Show,Typeable)

getX :: XY -> Nat
getX (XY x _) = x

getY :: XY -> Nat
getY (XY x y)
    | x == y    = S x
    | otherwise = y

instance Arbitrary XY where
    arbitrary = do
        x <- arbitrary
        y <- arbitrary
        return (XY x y)

whenSet :: Set -> Set
whenSet xs = if isSet xs then xs else NNil

-- Some unnecessary properties (?)
-- prop_isSet_add x s = isSet (add x (mkSet s)) =:= True
-- prop_isSet_del x s = isSet (del x (mkSet s)) =:= True
-- prop_isSet_mkSet s = isSet (mkSet s) =:= True
--
-- prop_whenSet_add x s = whenSet (add x (mkSet s)) =:= (add x (mkSet s))
-- prop_whenSet_del x s = whenSet (del x (mkSet s)) =:= (del x (mkSet s))
-- prop_whenSet_mkSet s = whenSet (mkSet s) =:= (mkSet s)

-- Some depth 4 properties
prop_del_comm x y s = del x (del y (whenSet s)) =:= del y (del x (whenSet s))
prop_add_comm x y s = add x (add y (whenSet s)) =:= add y (add x (whenSet s))

prop_isWhenSet s = isSet (whenSet s) =:= True
prop_isWhenSet_add x s = isSet (add x (whenSet s)) =:= True
prop_isWhenSet_del x s = isSet (del x (whenSet s)) =:= True

-- very false:
-- prop_del_set x s = whenSet (del x s) =:= whenSet s
-- prop_add_set x s = whenSet (add x s) =:= whenSet s

prop_add_del_comm :: XY -> Set -> Prop Set
prop_add_del_comm xy xs =
    add (getX xy) (del (getY xy) (whenSet xs)) =:=
    del (getY xy) (add (getX xy) (whenSet xs))

main = $(quickCheckAll)

