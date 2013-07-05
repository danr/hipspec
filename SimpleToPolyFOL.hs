module SimpleToPolyFOL where

import Simple
import PolyFOL

data Name a
    = Old a
    | Ptr a
    | App
    | Proj Int a
    -- + primitives for Int

trFun :: Function a -> [Clause (Name a)]
trFun (Function f tvs t as b) =
    [ TypeSig f'
  where
    f' = Old f

trBody :: Body a -> [Formula (Name a)]
trBody (Case e alts) =
