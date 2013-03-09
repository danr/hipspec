{-# LANGUAGE ParallelListComp #-}
{-

    Variable names that can be quantified over in axioms.

-}
module Halo.Names
    (mkVarNamesOfType
    ,mkVarNamesOfTypeWithOffset
    ,untypedVarNames
{-
    ,f,g,x
    ,f',g',x'
    ,varNames
-}
    ) where

import Type
import Id
import Name
import SrcLoc
import TysPrim
import Unique

-- import Halo.FOL.Abstract

import Control.Monad

-- | For disjointedness axioms, we need to put an offset to not make variables collide
mkVarNamesOfTypeWithOffset :: Int -> [Type] -> [Var]
mkVarNamesOfTypeWithOffset offset tys =
    [ mkLocalId
        (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
        ty
    | i <- [offset..]
    | n <- [1..] >>= flip replicateM "xyzwvu"
    | ty <- tys
    ]

mkVarNamesOfType :: [Type] -> [Var]
mkVarNamesOfType = mkVarNamesOfTypeWithOffset 0

untypedVarNames :: [Var]
untypedVarNames = mkVarNamesOfType (repeat anyTy)

{-
f,g,x :: Var
f:g:x:

-- the same as terms
f',g',x' :: Term'
[f',g',x'] = map qvar [f,g,x]
-}
