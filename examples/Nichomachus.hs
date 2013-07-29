module Nichomachus where

import Prelude (error)
import Nat hiding (sig)
import HipSpec
import Test.QuickSpec.Signature

sum :: Nat -> Nat
sum Z     = Z
sum (S n) = sum n + S n

cubes :: Nat -> Nat
cubes Z     = Z
cubes (S n) = cubes n + (S n * S n * S n)

prop_Nichomachus :: Nat -> Prop Nat
prop_Nichomachus n = cubes n =:= sum n * sum n

sig = [ vars ["x", "y", "z"] (error "Nat type" :: Nat)
      , fun0 "Z" Z
      , fun1 "S" S
      , fun2 "+" (+)
      , fun2 "*" (*)
      , fun1 "sum"   sum
      , fun1 "cubes" cubes
      , withTests 100
      , withQuickCheckSize 20
      ]

