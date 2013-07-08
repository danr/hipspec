{-# LANGUAGE PackageImports #-}
module DataConPattern where

import DataCon
import Var
import TyCon
import "ghc" Type

import Unify

dcAppliedTo :: Type -> DataCon -> ([TyVar],Maybe TvSubst)
dcAppliedTo t dc = (dc_tvs,mu)
  where
    dc_tvs = dataConUnivTyVars dc
    res_ty = dataConOrigResTy dc
    mu = tcUnifyTys (const BindMe) [res_ty] [t]

