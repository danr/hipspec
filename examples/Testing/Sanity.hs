{-# LANGUAGE DeriveDataTypeable #-}
module Sanity where

import HipSpec
import Prelude(Bool(..), Maybe(..), undefined, return, fmap, Eq, Ord)

tt :: Bool -> Bool -> Prop Bool
tt x y = x =:= True ==> y =:= True ==> x =:= y

bool_refl :: Bool -> Prop Bool
bool_refl x = x =:= x

bool_sym :: Bool -> Bool -> Prop Bool
bool_sym x y = x =:= y ==> y =:= x

bool_trans :: Bool -> Bool -> Bool -> Prop Bool
bool_trans x y z = x =:= y ==> y =:= z ==> x =:= z

maybe_refl :: Maybe Bool -> Prop (Maybe Bool)
maybe_refl x = x =:= x

maybe_sym :: Maybe Bool -> Maybe Bool -> Prop (Maybe Bool)
maybe_sym x y = x =:= y ==> y =:= x

maybe_trans :: Maybe Bool -> Maybe Bool -> Maybe Bool -> Prop (Maybe Bool)
maybe_trans x y z = x =:= y ==> y =:= z ==> x =:= z

test_and :: Bool -> Bool -> Prop Bool
test_and x y = x && y =:= True ==> y && x =:= True

consistency_0 :: Prop Bool
consistency_0 = (True =:= False)

consistency_1 :: Bool -> Prop Bool
consistency_1 x =  (x =:= False)

consistency_2 :: Maybe Bool -> Prop (Maybe Bool)
consistency_2 x =  (x =:= Nothing)

True  && a = a
False && a = False

True  || a = True
False || a = a

not True = False
not False = True

liftM k (Just x) = Just (k x)
liftM k Nothing  = Nothing

liftM2 k (Just x) (Just y) = Just (k x y)
liftM2 k _ _ = Nothing

mand = liftM2 (&&)
mor  = liftM2 (||)
mnot = liftM not

sig :: Sig
sig = signature
    [ vars ["a","b","c"]       (undefined :: Bool)
    , vars ["ma","mb","mc"]    (undefined :: Maybe Bool)

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

