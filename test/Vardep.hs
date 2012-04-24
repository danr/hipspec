module Vardep where

import Prelude()

data Maybe a = Just a | Nothing

data Nat = Succ Nat | Zero

Zero   + y = y
Succ x + y = Succ (x + y)

g x y = case x + y of
           Succ _ -> Just x
           Zero -> case y of
                       Zero   -> Nothing
                       Succ _ -> Just y    -- will never happen

h x y = case x + y of
           Succ z -> case y of Zero   -> Just x
                               Succ w -> Just y
           Zero -> Nothing

f x y = case y of Zero   -> case x of Zero   -> Nothing
                                      Succ _ -> Just x
                  Succ _ -> Just y

