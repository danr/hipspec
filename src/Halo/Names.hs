{-# LANGUAGE ParallelListComp #-}
{-

    Variable names that can be quantified over in axioms.

-}
module Halo.Names ( f,g,x,f',g',x',varNames ) where

import Id
import Name
import SrcLoc
import TysPrim
import Unique

import Halo.FOL.Abstract

import Control.Monad

-- | A bunch of variable names to quantify over
varNames :: [Var]
f,g,x :: Var
f:g:x:varNames =
    [ mkLocalId
        (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
        anyTy
    | i <- [0..]
    | n <- ["f","g","x"] ++ ([1..] >>= flip replicateM "xyzwvu")
    ]

-- the same as terms
f',g',x' :: Term'
[f',g',x'] = map qvar [f,g,x]
