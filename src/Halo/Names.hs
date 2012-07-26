{-# LANGUAGE ParallelListComp #-}
module Halo.Names ( f,g,x,f',g',x',varNames ) where

import Id
import Name
import SrcLoc
import Unique

import Halo.FOL.Abstract

import Control.Monad

-- | A bunch of variable names to quantify over
varNames :: [Var]
f,g,x :: Var
f:g:x:varNames =
    [ mkVanillaGlobal
        (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
        (error "varNames: type")
    | i <- [0..]
    | n <- ["f","g","x"] ++ ([1..] >>= flip replicateM "xyzwvu")
    ]

-- the same as terms
f',g',x' :: Term'
[f',g',x'] = map qvar [f,g,x]
