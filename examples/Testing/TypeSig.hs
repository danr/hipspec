{-

    $ hipspec TypeSig -m p
    Unknown result from z3 on prop coords:  0/1, exit code: ExitFailure 1
      stdout:
          (error "line 3 column 2: unknown sort 't_3c_Bool'")
          (error "line 9 column 4: unknown constant sk_c1XV_x")
          (error "line 13 column 4: unknown constant sk_c1XV_x")
          sat

-}
module TypeSig where

import HipSpec.Prelude

type Boolean = Bool

prop :: Boolean -> Prop Bool
prop x = x =:= x

