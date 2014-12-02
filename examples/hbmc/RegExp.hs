{-# LANGUAGE DeriveDataTypeable #-}
module RegExp where

import Control.Monad
import HipSpec
import Data.Typeable
import Data.Data

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :>: R a
  | Star (R a)
 deriving ( Eq, Ord, Show, Data, Typeable )

instance Arbitrary a => Arbitrary (R a) where
  arbitrary = sized go
    where
      go s = frequency
        [(1,return Nil)
        ,(1,return Eps)
        ,(3,Atom `fmap` arbitrary)
        ,(s,liftM2 (:+:) (go s2) (go s2))
        ,(s,liftM2 (:>:) (go s2) (go s2))
        ,(s,liftM  Star  (go s1))
        ]
        where
         s2 = s`div`2
         s1 = pred s

(.+.), (.>.) :: R a -> R a -> R a
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

Nil .>. q   = Nil
p   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

eps :: R a -> Bool
eps Eps       = True
eps (p :+: q) = eps p || eps q
eps (p :>: q) = eps p && eps q
eps (Star _)  = True
eps _         = False

epsR :: R a -> R a
epsR p | eps p     = Eps
       | otherwise = Nil

data C = A | B | C
 deriving ( Eq, Ord, Show, Data, Typeable )

instance Arbitrary C where
  arbitrary = elements [A,B,C]

-- step :: Eq a => R a -> a -> R a
step :: R C -> C -> R C
step (Atom a)  x | a == x = Eps
step (p :+: q) x          = step p x .+. step q x
step (p :>: q) x          = (step p x .>. q) .+. (epsR p .>. step q x)
step (Star p)  x          = step p x .>. Star p
step _         x          = Nil

-- rec :: Eq a => R a -> [a] -> Bool
rec :: R C -> [C] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs

prop_koen p q s = rec (p :>: q) s =:= rec (q :>: p) s

