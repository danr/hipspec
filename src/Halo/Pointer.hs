{-# LANGUAGE NamedFieldPuns #-}
{-

    Make a pointer subtheory

-}
module Halo.Pointer where

import Id

import Halo.FOL.Abstract

import Halo.Conf
import Halo.Names (varNames)
import Halo.Shared
import Halo.Subtheory

-- | Makes a pointer to a constructor or function, given its arity
mkPtr :: HaloConf -> Var -> Int -> Subtheory s
mkPtr HaloConf{ext_eq} h arity = Subtheory
    { provides    = Pointer h
    , depends     = AppOnMin : [ ExtensionalEquality | ext_eq ]
    , description = "Pointer axiom to " ++ showOutputable h
    , formulae    =
        let lhs = apps (ptr h) as'
            rhs = fun h as'
        in  [forall' as $ ors [min' lhs,min' rhs] ==> lhs === rhs]
    }
  where
    as  = take arity varNames
    as' = map qvar as
