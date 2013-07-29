module Iterate where

import Prelude (fmap,undefined,error,Eq,Ord)

import HipSpec.Prelude
import Test.QuickSpec.Signature hiding (total)

import List

id :: A -> A
id x = x

(.) :: (A -> A) -> (A -> A) -> A -> A
(f . g) x = f (g x)

ind :: List -> List
ind Nil      = Nil
ind (Cons x xs) = Cons x (ind xs)

map f Nil      = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

head (Cons x xs) = x
tail (Cons x xs) = xs

repeat x    = Cons x (repeat x)
iterate f x = Cons x (iterate f (f x))

cycle xs@Cons{} = xs ++ cycle xs

sig = signature
    [ pvars ["x","y","z"]    (undefined :: A)
    , pvars ["xs","ys","zs"] (undefined :: List)
    , vars1 ["f","g","h"]    (undefined :: A -> A)
    , blind0 "id" id
    , blind2 "."  (.)
    , "Nil"     `fun0` Nil
    , "Cons"    `fun2` Cons
    , "ind"     `fun1` ind
    , "++"      `fun2` (++)
    , "iterate" `fun2` iterate
    , "repeat"  `fun1` repeat
    , "map"     `fun2` map
    , "cycle"   `fun1` cycle
    , "head"    `fun1` head
    , "tail"    `fun1` tail
    , withQuickCheckSize 10
    ]

prop_huh :: A -> (A -> A) -> (A -> A) -> Prop List
prop_huh x f g = total x ==> total f ==> total g ==> iterate f x =:= iterate g x

prop_duh :: A -> A -> (A -> A) -> Prop List
prop_duh x y f = total x ==> total y ==> total f ==> iterate f x =:= iterate f y

