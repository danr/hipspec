{-# LANGUAGE DeriveDataTypeable #-}
module SameFringe where

import Prelude hiding (reverse,(++),length,map,filter,(.),(+),const,(==),Enum,(&&))
import Control.Applicative
import qualified Prelude
import HipSpec
-- import Nat hiding (sig)

data List = Cons AB List | Nil
  deriving (Eq,Typeable,Ord,Show)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

data AB = A | B
  deriving (Eq,Typeable,Ord,Show)

instance Arbitrary AB where
    arbitrary = elements [A,B]

data Tree = Branch Tree AB Tree | Empty
  deriving (Eq,Typeable,Ord,Show)

inorder :: Tree -> List
inorder (Branch l x r) = inorder l ++ Cons x (inorder r)
inorder Empty          = Nil

data Enum
    = Done
    | Next AB Enum Tree
  deriving (Eq,Typeable,Ord,Show)

_a  = Branch Empty A Empty
_b  = Branch Empty B Empty

t1  = Branch _a B Empty
t2  = Branch Empty A _b

enum :: Tree -> Enum -> Enum
enum Empty          e = e
enum (Branch l x r) e = enum l (Next x e r)

sameFringe :: Tree -> Tree -> Bool
sameFringe t1 t2 = sameEnum (enum t1 Done) (enum t2 Done)

sameEnum :: Enum -> Enum -> Bool
sameEnum Done            Done            = True
sameEnum (Next b1 e1 t1) (Next b2 e2 t2)
    = b1 == b2 && sameEnum e1 e2 && sameFringe t1 t2
sameEnum Done            Next{} = False
sameEnum Next{}          Done   = False

(==) :: AB -> AB -> Bool
A == A = True
B == B = True
A == B = False
B == A = False

(&&) :: Bool -> Bool -> Bool
True  && a = a
False && b = False

sig = signature
    [fun0 "False" False
	,fun0 "True" True
	,fun0 "Nil" (SameFringe.Nil)
	,fun3 "Next" (SameFringe.Next)
	,fun0 "Empty" (SameFringe.Empty)
	,fun3 "Branch" (SameFringe.Branch)
	,fun2 "Cons" (SameFringe.Cons)
	,fun0 "Done" (SameFringe.Done)
	,fun2 "sameFringe" (SameFringe.sameFringe)
	,fun2 "sameEnum" (SameFringe.sameEnum)
	,fun1 "inorder" (SameFringe.inorder)
	,fun2 "enum" (SameFringe.enum)
	,fun2 "++" (SameFringe.++)
	,vars ["a","b","c"] (Prelude.undefined :: Bool)
	,vars ["xs","ys","zs"] (Prelude.undefined :: SameFringe.List)
	,vars ["e","e2","e3"] (Prelude.undefined :: SameFringe.Enum)
	,vars ["t","u","v"] (Prelude.undefined :: SameFringe.Tree)
	,withTests 100
	,withQuickCheckSize 20
	,withSize 1000]

instance Names Tree where
    names _ = ["t","u","v"]

instance Names Enum where
    names _ = ["e","e2","e3"]

instance Names List where
    names _ = ["xs","ys","zs"]

prop_sameFringe t1 t2 xs
    = xs =:= inorder t1 ==> xs =:= inorder t2 ==> sameFringe t1 t2 =:= True

prop_sameFringe' t1 t2
    = sameFringe t1 t2 =:= True ==> inorder t1 =:= inorder t2

prop_sameFringe'' t1 t2
    = inorder t1 =:= inorder t2 ==> sameFringe t1 t2 =:= True

instance Arbitrary List where
    arbitrary = toList `fmap` arbitrary

instance Arbitrary Tree where
    arbitrary = sized arbTree

instance Arbitrary Enum where
    arbitrary = flip enum Done <$> arbitrary

arbTree :: Int -> Gen Tree
arbTree s = frequency
    [ (s,Branch <$> arbTree (s `div` 2) <*> arbitrary <*> arbTree (s `div` 2))
    , (1,return Empty)
    ]

fromList :: List -> [AB]
fromList (Cons x xs) = x : fromList xs
fromList Nil         = []

toList :: [AB] -> List
toList (x:xs) = Cons x (toList xs)
toList []     = Nil

