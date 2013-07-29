module Where where

k x y = x

f x y = k m m
  where m = k x x

-- No scoping
g x y = k (n x)
  where n y = k x y

-- Scoping;
h x y = k (m x)
  where m x = k x y

