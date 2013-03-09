{-# LANGUAGE NamedFieldPuns #-}
{-

    Make a pointer subtheory

-}
module Halo.Pointer where

import Id
import Var

import Halo.FOL.Abstract
import Halo.FOL.Operations

import Halo.Names
import Halo.Shared
import Halo.Subtheory
import Halo.MonoType

-- | Makes a pointer to a constructor or function
--   Uses varType to get its type
mkPtr :: Monad m => Var -> m (Subtheory s)
mkPtr h = do

    ty <- monoType (varType h)

    let arg_tys = typeArgs ty
        arity   = length arg_tys
        args    = take arity untypedVarNames
        args'   = map qvar args
        tyargs  = zip args arg_tys

    lhs <- apps ty (ptr h ty) args'
    let rhs = apply h args'
        formula = forall' tyargs $ lhs === rhs

    return subtheory
        { provides    = Pointer h
        , depends     = []
        , description = "Pointer axiom to " ++ showOutputable h
        , formulae    = [formula]
        }

