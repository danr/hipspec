{-# LANGUAGE TemplateHaskell #-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO, Maybe(..), undefined, return, fmap)

test :: Bool -> Prop Bool
test x = givenBool x (proveBool x)

refl :: a -> Prop a
refl x = x =:= x

sym :: a -> a -> Prop a
sym x y = x =:= y ==> y =:= x

trans :: a -> a -> a -> Prop a
trans x y z = x =:= y ==> y =:= z ==> x =:= z

bool_refl x = refl x :: Prop Bool
bool_sym x y = sym x y :: Prop Bool
bool_trans x y z = trans x y z :: Prop Bool

bool_list_refl x = refl x :: Prop [Bool]
bool_list_sym x y = sym x y :: Prop [Bool]
bool_list_trans x y z = trans x y z :: Prop [Bool]

maybe_bool_refl x = refl x :: Prop (Maybe Bool)
maybe_bool_sym x y = sym x y :: Prop (Maybe Bool)
maybe_bool_trans x y z = trans x y z :: Prop (Maybe Bool)

maybe_bool_list_refl x = refl x :: Prop [(Maybe Bool)]
maybe_bool_list_sym x y = sym x y :: Prop [(Maybe Bool)]
maybe_bool_list_trans x y z = trans x y z :: Prop [(Maybe Bool)]

test_and :: Bool -> Bool -> Prop Bool
test_and x y = x && y =:= True ==> y && x =:= True

consistency :: Prop Bool
consistency = oops (True =:= False)

True  && a = a
False && a = False

True  || a = a
False || a = False

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith k (x:xs) (y:ys) = k x y : zipWith k xs ys
zipWith k _ _ = []

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x:map f xs

not True = False
not False = True

liftM k (Just x) = Just (k x)
liftM k Nothing  = Nothing

liftM2 k (Just x) (Just y) = Just (k x y)
liftM2 k _ _ = Nothing

mand = liftM2 (&&)
mor  = liftM2 (||)
mnot = liftM not

nothing :: Maybe Bool
nothing = Nothing

main :: IO ()
main = hipSpec $(fileName)
    [ pvars ["a","b","c"]       (undefined :: Bool)
    , pvars ["ma","mb","mc"]    (undefined :: Maybe Bool)
    , pvars ["as","bs","cs"]    (undefined :: [Bool])
    , pvars ["mas","mbs","mcs"] (undefined :: Maybe [Bool])
    , pvars ["xs","ys","zs"]    (undefined :: [A])

    , fun0 "True" True
    , fun0 "False" False

    , fun1 "Just"    (Just :: A -> Maybe A)
    , fun0 "Nothing" (Nothing :: Maybe A)

    , fun1 "Just"    (Just :: Bool -> Maybe Bool)
    , fun0 "Nothing" (Nothing :: Maybe Bool)

    , fun2 ":"       ((:)  :: A   -> [A]   -> [A])
    , fun0 "[]"      ([]   :: [A])

    , fun2 ":"       ((:)  :: Maybe A   -> [Maybe A]   -> [Maybe A])
    , fun0 "[]"      ([]   :: [Maybe A])

    , fun2 ":"       ((:)  :: Bool   -> [Bool]   -> [Bool])
    , fun0 "[]"      ([]   :: [Bool])

    , fun2 ":"       ((:)  :: Maybe Bool   -> [Maybe Bool]   -> [Maybe Bool])
    , fun0 "[]"      ([]   :: [Maybe Bool])

    , fun2 "map"     (map     :: (A -> A) -> [A] -> [A])
    , fun3 "zipWith" (zipWith :: (A -> A -> A) -> [A] -> [A] -> [A])

    , fun2 "map"     (map     :: (Maybe A -> Maybe A) -> [Maybe A] -> [Maybe A])
    , fun3 "zipWith" (zipWith :: (Maybe A -> Maybe A -> Maybe A) -> [Maybe A] -> [Maybe A] -> [Maybe A])

    , fun2 "map"     (map     :: (Bool -> Bool) -> [Bool] -> [Bool])
    , fun3 "zipWith" (zipWith :: (Bool -> Bool -> Bool) -> [Bool] -> [Bool] -> [Bool])

    , fun2 "map"     (map     :: (Maybe Bool -> Maybe Bool) -> [Maybe Bool] -> [Maybe Bool])
    , fun3 "zipWith" (zipWith :: (Maybe Bool -> Maybe Bool -> Maybe Bool) -> [Maybe Bool] -> [Maybe Bool] -> [Maybe Bool])

    , fun2 "&&" (&&)
    , fun2 "||" (||)
    , fun1 "not" not

    , fun2 "mand" mand
    , fun2 "mor"  mor
    , fun1 "mnot" mnot

    , withTests 10
    ]

instance Partial a => Partial (Maybe a) where
  unlifted Nothing  = return Nothing
  unlifted (Just x) = fmap Just (lifted x)

