module DepthTwoCase where

data T = B T T | E

foo (B (B x y) w) = True
foo (B x       w) = False
