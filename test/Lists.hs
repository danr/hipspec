module Lists where

import Prelude(undefined)

map f xs = [ f x | x <- xs ]

-- Introduces a let, so it does not work:
-- concatMap f xss = [ f x | xs <- xss, x <- xs ]

filter p xs = [ x | x <- xs, p x ]

