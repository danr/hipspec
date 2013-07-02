module List where

data List a = Cons a (List a) | Nil

head :: List Bool -> Bool
head (Cons x _) = x
head Nil        = False

head' :: [Bool] -> Bool
head' (x:_) = x
head' []    = False
