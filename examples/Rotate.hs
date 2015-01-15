module Rotate where

import Prelude hiding ((++),length,(+))
import QuickSpec hiding (S,Prop)

import HipSpec

import Nat (Nat(..),(+))
import List ((++),length)

rotate :: Nat -> [a] -> [a]
rotate Z     xs     = xs
rotate _     []     = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

-- prop_rotate :: [a] -> Prop [a]
prop_rotate xs = rotate (length xs) xs =:= xs

sig :: Signature
sig = signature
    { constants =
        [ constant "Z" Z
        , (constant "S" S) { conStyle = Uncurried }
        , (constant "length" (length :: [A] -> Nat)) { conStyle = Uncurried }
        , constant "++" ((++) :: [A] -> [A] -> [A])
        , constant ":" ((:) :: A -> [A] -> [A])
        , constant "[]" ([] :: [A])
        , constant "rotate" (rotate :: Nat -> [A] -> [A])
        ]
    , instances = [ baseType (undefined :: Nat) ]
    }
