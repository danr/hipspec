{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO, undefined, return, fmap, Eq, Ord)

data MaybeBool = Just Bool | Nothing
  deriving (Eq,Ord,Typeable)

test :: Bool -> Prop Bool
test x = givenBool x (proveBool x)

bool_refl :: Bool -> Prop Bool
bool_refl x = x =:= x

bool_sym :: Bool -> Bool -> Prop Bool
bool_sym x y = x =:= y ==> y =:= x

bool_trans :: Bool -> Bool -> Bool -> Prop Bool
bool_trans x y z = x =:= y ==> y =:= z ==> x =:= z

maybe_refl :: MaybeBool -> Prop MaybeBool
maybe_refl x = x =:= x

maybe_sym :: MaybeBool -> MaybeBool -> Prop MaybeBool
maybe_sym x y = x =:= y ==> y =:= x

maybe_trans :: MaybeBool -> MaybeBool -> MaybeBool -> Prop MaybeBool
maybe_trans x y z = x =:= y ==> y =:= z ==> x =:= z

test_and :: Bool -> Bool -> Prop Bool
test_and x y = x && y =:= True ==> y && x =:= True

consistency_0 :: Prop Bool
consistency_0 =  (True =:= False)

consistency_1 :: Bool -> Prop Bool
consistency_1 x =  (x =:= False)

consistency_2 :: MaybeBool -> Prop MaybeBool
consistency_2 x =  (x =:= Nothing)

True  && a = a
False && a = False

True  || a = a
False || a = False

not True = False
not False = True

liftM k (Just x) = Just (k x)
liftM k Nothing  = Nothing

liftM2 k (Just x) (Just y) = Just (k x y)
liftM2 k _ _ = Nothing

mand = liftM2 (&&)
mor  = liftM2 (||)
mnot = liftM not

main :: IO ()
main = hipSpec $(fileName)
    [ pvars ["a","b","c"]       (undefined :: Bool)
    , pvars ["ma","mb","mc"]    (undefined :: MaybeBool)

    , fun0 "True" True
    , fun0 "False" False

    , fun2 "&&" (&&)
    , fun2 "||" (||)
    , fun1 "not" not

    , fun2 "mand" mand
    , fun2 "mor"  mor
    , fun1 "mnot" mnot

--    , withTests 10
    ]

instance Arbitrary MaybeBool where
    arbitrary = elements [Nothing,Just True,Just False]

instance Partial MaybeBool where
    unlifted Nothing  = return Nothing
    unlifted (Just x) = fmap Just (lifted x)

