{-# LANGUAGE DeriveDataTypeable,TemplateHaskell #-}
module Main where

import Prelude hiding (reverse,(++),length)

import Data.Typeable

import HipSpec
import HipSpec.Prelude

data Nat = S Nat | Z
  deriving (Eq,Show,Typeable,Ord)

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ [x]
reverse []     = []

main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] intType
    , vars ["m", "n", "o"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] listType
    , fun0 "[]"       ([]       :: [A])
    , fun2 ":"        ((:)      :: A  -> [A] -> [A])
    , fun2 "++"       ((++)     :: [A] -> [A] -> [A])
    , fun1 "reverse"  (reverse  :: [A] -> [A])
    , fun1 "length"   (length   :: [A] -> Nat) 
    , fun0 "Z" Z
    , fun1 "S" S
    ]
  where
    intType   = intType  :: A
    listType  = listType :: [A]

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized arbSized

arbSized s = do
  x <- choose (0,round (sqrt (toEnum s)))
  return (toEnum x)
