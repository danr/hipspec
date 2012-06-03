{-|

   Builtin types, [a], Bool, (), (a,b)

-}
module Hip.BuiltinTypes where

import BasicTypes
import GHC
import TysWiredIn

builtins :: [TyCon]
builtins = listTyCon : boolTyCon : unitTyCon
        : map (tupleTyCon BoxedTuple) [2..2]
        -- ^ choice: only tuples of size 2 supported!!
        --   TODO:   add a lot of sizes in dependencies
        --           and do proper data dependency
