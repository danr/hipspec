module Lambdas where

import Prelude hiding (map)

-- Local, recursive function that needs to be lifted to the top level
map f xs = go xs
  where
    go (x:xs) = f x : go xs
    go []     = []

-- Lambda function that needs to be lifted
-- Interestingly, with optimisation, the body of map gets inlined
singletons = map (:[])

