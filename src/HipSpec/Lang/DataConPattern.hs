
module HipSpec.Lang.DataConPattern where

import DataCon
import Var
import Type
import TyCon

import Unify

import VarSet

dcAppliedTo :: Type -> DataCon -> ([TyVar],Maybe TvSubst)
dcAppliedTo t dc = (dc_tvs,mu)
  where
    dc_tvs = dataConUnivTyVars dc
    res_ty = dataConOrigResTy dc
    mu = tcMatchTy (mkVarSet dc_tvs) res_ty t

