module Eithers where

import Prelude ()

data Either a b = Left a | Right b

silly :: Either [a] [b] -> [Either a b]
silly (Left as)  = [ Left a | a <- as ]
silly (Right bs) = [ Right b | b <- bs ]

