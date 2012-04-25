module Shadowing where

d p = case p of
  p -> d p
  _ -> p

data Nat = Succ Nat | Zero

pred x = case x of
    Succ x -> x
    Zero   -> x

predpred x = case x of
    Succ x -> case x of
        Succ x -> x
        Zero   -> x
    Zero -> x

predhead x = case x of
    x : xs -> case x of
       Succ x -> x : xs
       Zero   -> x : xs
    []     -> []