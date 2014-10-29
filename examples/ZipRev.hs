module ZipRev where

import Prelude hiding ((++),zip)
import HipSpec
import Nat (Nat(..))

len :: [a] -> Nat
len []     = Z
len (_:xs) = S (len xs)

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

rev :: [a] -> [a]
rev (x:xs) = rev xs ++ [x]
rev []     = []

zip :: [a] -> [b] -> [(a,b)]
zip (x:xs) (y:ys) = (x,y):zip xs ys
zip []     _      = []
zip _      []     = []

isaplanner_no_85 xs ys = len xs =:= len ys ==> zip (rev xs) (rev ys) =:= rev (zip xs ys)

-- Synthesised by Nick:
nicks_lemma xs ys as bs = len xs =:= len ys ==> zip xs ys ++ zip as bs =:= zip (xs ++ as) (ys ++ bs)

-- Standard stuff, until QuickSpec bug is fixed:
app_assoc xs ys zs = xs ++ (ys ++ zs) =:= (xs ++ ys) ++ zs

app_rid xs = xs ++ [] =:= xs

len_morph xs ys = len (xs ++ ys) =:= len (ys ++ xs)

rev_len xs = len (rev xs) =:= len xs

rev_morph xs ys = rev xs ++ rev ys =:= rev (ys ++ xs)

rev_rev xs = rev (rev xs) =:= xs
