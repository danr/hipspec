module Filter where

import Prelude (Bool(..))

data Nat = Succ Nat | Zero
data List a = Nil | Cons a (List a)

filter0 p Nil = Nil
filter0 p (x `Cons` xs) = case p x of
                     True  -> x `Cons` filter0 p xs
                     False -> filter0 p xs

filter1 p Nil = Nil
filter1 p (x `Cons` xs) = case p x of
                     True  -> x `Cons` rest
                     False -> rest
  where rest = filter1 p xs

filter2 p Nil = Nil
filter2 p (x `Cons` xs) | p x = x `Cons` filter2 p xs
filter2 p (x `Cons` xs) = filter2 p xs


