-- Properties of infinite objects
module Infinity where

import HipPrelude
import Prelude (Bool(..),(&&),(==),div,Eq,Show,return,Int,pred)
import Control.Monad (liftM3)

data Tree a = Empty | Branch (Tree a) a (Tree a)
  deriving (Show)

instance Eq a => Eq (Tree a) where
  t1 == t2 = trim 10 t1 `eq` trim 10 t2
    where
      trim 0 _     = Empty
      trim n Empty = Empty
      trim n (Branch l x r) = Branch (trim (pred n) l) x (trim (pred n) r)

      eq Empty Empty = True
      eq (Branch l x r) (Branch l' x' r') = eq l l' && x == x' && eq r r'

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized arbTree
    where
      arbTree s = frequency [(1,return Empty)
                            ,(s',liftM3 Branch (arbTree s')
                                               arbitrary
                                               (arbTree s'))
                            ] where s' = s `div` 2

(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x = f (g x)

id x = x

map :: (a -> b) -> [a] -> [b]
map f []       = []
map f (x : xs) = f x : map f xs

concat :: [[a]] -> [a]
concat []           = []
concat ([]:xss)     = concat xss
concat ((x:xs):xss) = x : concat (xs:xss)

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) | p x = x : (filter p xs)
filter p (x:xs) = filter p xs

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

repeat :: a -> [a]
repeat x = x : repeat x

cycle :: [a] -> [a]
cycle xs = xs ++ cycle xs

tail :: [a] -> [a]
tail [x]    = []
tail (x:xs) = x:tail xs

prop_map_iterate :: (a -> a) -> a -> Prop [a]
prop_map_iterate f x = map f (iterate f x) =:= iterate f (f x)

{-
prop_filter_iterate :: (a -> Bool) -> (a -> a) -> a -> Prop [a]
prop_filter_iterate p f x = filter p (iterate f (f x)) =:=
                            filter (p . f) (iterate f x)
-}

prop_repeat_iterate :: a -> Prop [a]
prop_repeat_iterate x = repeat x =:= iterate id x

prop_repeat_cycle_singleton :: a -> Prop [a]
prop_repeat_cycle_singleton x = repeat x =:= cycle [x]

-- List needs to be nonempty
prop_concat_repeat_cycle :: a -> [a] -> Prop [a]
prop_concat_repeat_cycle x xs = concat (repeat (x:xs)) =:= cycle (x:xs)

prop_tail_repeat :: a -> Prop [a]
prop_tail_repeat x = repeat x =:= tail (repeat x)

iterTree :: (a -> a) -> (a -> a) -> a -> Tree a
iterTree f g x = Branch (iterTree f g (f x)) x (iterTree f g (g x))

fmap :: (a -> b) -> Tree a -> Tree b
fmap f Empty = Empty
fmap f (Branch l x r) = Branch (fmap f l) (f x) (fmap f r)

repeatTree :: a -> Tree a
repeatTree x = Branch (repeatTree x) x (repeatTree x)

mirror :: Tree a -> Tree a
mirror (Branch l x r) = Branch (mirror r) x (mirror l)
mirror Empty          = Empty

traverse :: Tree a -> [a]
traverse (Branch l x r) = traverse l ++ [x] ++ traverse r
traverse Empty          = []

toList :: Tree a -> [a]
toList (Branch l x r) = x : toList l ++ toList r
toList Empty          = []

reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

prop_fmap_iterate :: (a -> a) -> a -> Prop (Tree a)
prop_fmap_iterate f x = fmap f (iterTree f f x) =:= iterTree f f (f x)

prop_fmap_comp :: (b -> c) -> (a -> b) -> Tree a -> Prop (Tree c)
prop_fmap_comp f g t = fmap (f . g) t =:= fmap f (fmap g t)

prop_fmap_left :: (a -> b) -> Tree a -> Prop (Tree b)
prop_fmap_left f t = fmap (id . f) t =:= fmap f t

prop_fmap_right :: (a -> b) -> Tree a -> Prop (Tree b)
prop_fmap_right f t = fmap (f . id) t =:= fmap f t

prop_fmap_id :: Tree a -> Prop (Tree a)
prop_fmap_id t = fmap id t =:= t

prop_mirror_involutive :: Tree a -> Prop (Tree a)
prop_mirror_involutive t = mirror (mirror t) =:= t

prop_mirror_iterate :: a -> (a -> a) -> (a -> a) -> Prop (Tree a)
prop_mirror_iterate x f g = mirror (iterTree f g x) =:= iterTree g f x

prop_fmap_map_traverse :: Tree a -> (a -> b) -> Prop [b]
prop_fmap_map_traverse t f = map f (traverse t) =:= traverse (fmap f t)

prop_fmap_map_toList :: Tree a -> (a -> b) -> Prop [b]
prop_fmap_map_toList t f = map f (toList t) =:= toList (fmap f t)

prop_mirror_traverse_rev :: Tree a -> Prop [a]
prop_mirror_traverse_rev t = reverse (traverse t) =:= traverse (mirror t)

main = do
  quickCheck (printTestCase "prop_map_iterate"            (prop_map_iterate            :: (Int -> Int) -> Int -> Prop [Int]))
--  quickCheck (printTestCase "prop_filter_iterate"       (prop_filter_iterate         :: (Int -> Bool) -> (Int -> Int) -> Int -> Prop [Int]))
  quickCheck (printTestCase "prop_repeat_iterate"         (prop_repeat_iterate         :: Int -> Prop [Int]))
  quickCheck (printTestCase "prop_repeat_cycle_singleton" (prop_repeat_cycle_singleton :: Int -> Prop [Int]))
  quickCheck (printTestCase "prop_concat_repeat_cycle"    (prop_concat_repeat_cycle    :: Int -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_tail_repeat"            (prop_tail_repeat            :: Int -> Prop [Int]))
  quickCheck (printTestCase "prop_fmap_iterate"           (prop_fmap_iterate           :: (Int -> Int) -> Int -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_fmap_comp"              (prop_fmap_comp              :: (Int -> Int) -> (Int -> Int) -> Tree Int -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_fmap_left"              (prop_fmap_left              :: (Int -> Int) -> Tree Int -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_fmap_right"             (prop_fmap_right             :: (Int -> Int) -> Tree Int -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_fmap_id"                (prop_fmap_id                :: Tree Int -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_mirror_involutive"      (prop_mirror_involutive      :: Tree Int -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_mirror_iterate"         (prop_mirror_iterate         :: Int -> (Int -> Int) -> (Int -> Int) -> Prop (Tree Int)))
  quickCheck (printTestCase "prop_fmap_map_traverse"      (prop_fmap_map_traverse      :: Tree Int -> (Int -> Int) -> Prop [Int]))
  quickCheck (printTestCase "prop_fmap_map_toList"        (prop_fmap_map_toList        :: Tree Int -> (Int -> Int) -> Prop [Int]))
  quickCheck (printTestCase "prop_mirror_traverse_rev"    (prop_mirror_traverse_rev    :: Tree Int -> Prop [Int]))
