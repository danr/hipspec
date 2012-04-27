module Xor where

import Prelude (Bool(..))

xor b = case b of True -> not'
                  False -> id'
 where
  not' True  = False
  not' False = True

  id' x = x

{-# NOINLINE not #-}
not True  = False
not False = True

{-# NOINLINE id #-}
id x = x

xor2 True = not
xor2 False = id


