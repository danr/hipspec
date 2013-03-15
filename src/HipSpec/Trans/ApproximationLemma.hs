{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.ApproximationLemma(approximate) where

import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop

import Control.Concurrent.STM.Promise.Tree

import Halo.FOL.Abstract hiding (Term)
import Halo.Binds
import Halo.Util
import Halo.MonoType
import Halo.Monad

import Control.Monad.Reader

import CoreSyn
import DataCon
import Type
import Var

import HipSpec.Trans.MakerMonad
import HipSpec.Trans.Literal

import MkCore
import TyCon
import Id
import Name
import OccName as OccName

approximate :: forall eq . Property eq -> Maybe (MakerM (ProofTree eq))
approximate prop@Property{..} = do
    (e1,e2) <- propCoreExprEquation prop
    (ty_con,_arg_tys) <- splitTyConApp_maybe propType
    guard (isDataTyCon ty_con)
    return $ do
        (approx,rec,e) <- mkApproxFun ty_con

        (fs,deps) <- lift $ do

            approx_thy:_ <- trBind e
            let approx_fs   = formulae approx_thy
                approx_deps = filter (`notElem` map Function [approx,rec])
                                     (depends approx_thy)

            local (addQuantVars (map fst propVars)) $ do

                hyp_tr_lit  <- trLiteral (App (Var rec) e1 :== App (Var rec) e2)
                conc_tr_lit <- trLiteral (App (Var approx) e1 :== App (Var approx) e2)

                hyp_fs  <- foralls varMonoType hyp_tr_lit
                conc_fs <- foralls varMonoType conc_tr_lit

                return (hyp_fs:neg conc_fs:approx_fs,approx_deps)

        monoty <- varMonoType approx

        return $ Leaf $ Obligation
            { ob_prop = prop
            , ob_info = ApproxLemma
            , ob_content = calculateDeps subtheory
                { provides    = Specific Conjecture
                , depends     = deps ++ propDeps
                , description = "Approximation conjecture for " ++ propName
                , formulae    = fs
                , typedecls   = zip [approx,rec] (repeat monoty)
                }
            }

-- TODO: what about instantiation?
mkApproxFun :: TyCon -> MakerM (Var,Var,CoreBind)
mkApproxFun ty_con = do
    approx <- mk_id "approx" fn_ty <$> makeUnique
    rec    <- mk_id "rec" fn_ty <$> makeUnique
    arg    <- mk_id "x" tycon_ty <$> makeUnique

    alts <- mapM (alt rec) (tyConDataCons ty_con)

    let body = mkCoreLams (ty_vars ++ [arg])
                          (Case (Var arg) arg tycon_ty alts)

    return (approx,rec,NonRec approx body)
  where

    alt :: Var -> DataCon -> MakerM (AltCon,[Var],CoreExpr)
    alt rec dc = do
        let dc_tys = dataConOrigArgTys dc
        args <- sequence [ mk_id "y" ty <$> makeUnique | ty <- dc_tys ]
        let body = mkCoreConApps dc $
                        map varToCoreExpr ty_vars ++
                        [ if varType arg `eqType` tycon_ty
                            then mkVarApps (Var rec) (ty_vars ++ [arg])
                            else Var arg
                        | arg <- args ]
        return (DataAlt dc,args,body)

    ty_vars = tyConTyVars ty_con

    -- approx :: forall tys . K tys -> K tys
    tycon_ty = mkTyConApp ty_con (map mkTyVarTy ty_vars)
    fn_ty    = mkForAllTys ty_vars (mkFunTy tycon_ty tycon_ty)

    mk_id n ty u = mkLocalId (mkSystemName u (mkOccName OccName.varName n)) ty

