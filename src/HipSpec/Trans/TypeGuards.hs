{-# LANGUAGE PatternGuards #-}
module HipSpec.Trans.TypeGuards where

import Var
import Id
import TyCon
import Type
import TysPrim

import Halo.FOL.Abstract
import Halo.FOL.Internals.Internals
import Halo.Util
import Halo.Shared

import HipSpec.Trans.Types

import Data.List
import Data.Generics.Geniplate


trType :: Type -> ([TyVar],Term')
trType ty0 = second go (splitForAllTys ty0)
  where
    go ty
        | Just (t1,t2)  <- splitFunTy_maybe ty    = apply (tyConVar funTyCon)
                                                          (map go [t1,t2])
        | Just (tc,tys) <- splitTyConApp_maybe ty = apply (tyConVar tc)
                                                          (map go tys)
        | Just tyv      <- getTyVar_maybe ty      = qvar tyv
        | otherwise
            = error $ "HipSpec.Trans.TypeGuards.trType: " ++
                "Can only translate top-level foralls, " ++
                "type and function constructors and type variables, " ++
                "but not this type: " ++ showOutputable ty ++ ", " ++
                "originiating from " ++ showOutputable ty0

    tyConVar ty_con = mkLocalId (tyConName ty_con) anyTy

typeGuardFormula :: Formula' -> Formula'
typeGuardFormula = transform $ \fm ->
    case fm of
        Forall qs f ->
            let (new_quant,guards) = first (nub . concat) $ unzip
                    [ (ty_quant,isType (qvar q) tr_type)
                    | q <- qs
                    , let ty = varType q
                    , finiteType ty
                    , let (ty_quant,tr_type) = trType ty
                    ]
            in  forall' (qs ++ new_quant) (guards ===> f)
        _ -> fm

typeGuardSkolem :: Var -> Maybe Formula'
typeGuardSkolem v
    | finiteType ty =
        let (ty_quant,tr_type) = trType ty
        in  Just (forall' ty_quant (isType (skolem v) tr_type))
    | otherwise = Nothing
  where
    ty = varType v

