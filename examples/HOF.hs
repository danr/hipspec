{-# LANGUAGE ExplicitForAll #-}
module HOF where

import HipSpec
import Prelude hiding (zipWith,curry,map,zip)

p f = id . f =:= f . id

op f x y = f x y

r = op const =:= \ x y -> x

q f g = id . f . g =:= f . g

