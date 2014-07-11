module HipSpec.Fuel where

import HipSpec.Lang.Simple as S
import HipSpec.Id

addFuelArguments :: [S.Function Id] -> [S.Function Id]
addFuelArguments fns =
    [
    | S.Function fn (S.Forall tvs t)
    ]
