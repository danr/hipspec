module Main where

import Hip.HipSpec
import Prelude hiding ((&&),(||),not)

True  && a = a
False && _ = False

False || a = a
True  || _ = True

not True  = False
not False = True

main = hipSpec "Bool.hs" conf 3
  where conf = describe "Bool"
                [ var "x" (undefined :: Bool)
                , var "y" (undefined :: Bool)
                , var "z" (undefined :: Bool)
                , con "&&" (&&)
                , con "||" (||)
                , con "not" not
                , con "True" True
                , con "False" False
                ]

