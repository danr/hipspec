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
import Halo.Names (varNames)

import HipSpec.Trans.Types

import Data.Maybe
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

-- Maybe makes a guard for a variable
makeGuard :: (Var -> Term') -> Var -> Maybe ([Var],Formula')
makeGuard mk q
    | finiteType ty =
        let (ty_quant,tr_type) = trType ty
        in  Just (ty_quant,isType (mk q) tr_type)

    | Just (args,res) <- finiteFunctionResult ty =
        let new_quant = zipWith setVarType varNames args
            (ty_quant,tr_type) = trType res
            phi = forall' new_quant
                          (isType (apps (mk q) (map qvar new_quant))
                                  tr_type)
        in  Just (ty_quant, phi)

    | otherwise = Nothing
  where
    ty = varType q

typeGuardFormula :: Formula' -> Formula'
typeGuardFormula = transform $ \fm ->
    case fm of
        Forall qs f ->
            let (new_quants,guards) = unzip $ mapMaybe (makeGuard qvar) qs
                new_quant = nubSorted (concat new_quants)
            in  forall' (qs ++ new_quant) (guards ===> f)
        _ -> fm

typeGuardSkolem :: Var -> Maybe Formula'
typeGuardSkolem v = do
    (ty_quant,phi) <- makeGuard skolem v
    return $ forall' ty_quant phi

