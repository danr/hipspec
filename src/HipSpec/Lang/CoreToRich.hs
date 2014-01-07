{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances #-}

-- | Translation from GHC Core to the Rich HipSpec.Language, a subset
module HipSpec.Lang.CoreToRich where

import Control.Applicative
import Control.Monad.Error

import HipSpec.Lang.Rich as R
import HipSpec.Lang.Type as R

import CoreUtils as C
import CoreSyn as C

import DataCon
import Literal
import Var hiding (Id)
import TyCon hiding (data_cons)
import Type as C
import GHC (dataConType)
import FastString (unpackFS)

import HipSpec.Lang.DataConPattern

import IdInfo

import HipSpec.GHC.Utils (showOutputable)

import HipSpec.Lang.TyAppBeta

import HipSpec.Id

-- | The binders in our translated expressions.
--
--   We cannot use 'Var'/'Id' because 'TyCon's do not have them,
--   and 'DataCon's does not necessarily have a unique.
--   'Name's have, just as 'Var'/'Id', a 'Unique' in them.
--
--   The types need to be remembered so we used typed

type TM a = Either String a

msgUnsupportedLiteral l    = "Unsupported literal: " ++ showOutputable l
msgIllegalType t           = "Illegal type: " ++ showOutputable t
msgTypeApplicationToExpr e = "Type application to expression: " ++ showOutputable e
msgTypeExpr e              = "Type expression: " ++ showOutputable e
msgCoercionExpr e          = "Coercion expression: " ++ showOutputable e
msgCastExpr e              = "Cast expression: " ++ showOutputable e
msgHigherRankType v t      = showOutputable v ++ " has a higher-rank type: " ++ showOutputable t
msgUnificationError t tvs dc e mu =
       "Unification error on " ++ showOutputable t
       ++ "\nWhen resolving type variables " ++ showOutputable tvs
       ++ " for constructor " ++ showOutputable dc ++
       (case mu of
           Just u -> "\nObtained unifier: " ++ showOutputable u
           Nothing -> " without unifier")
       ++ "\nOriginating from expression: " ++ showOutputable e
msgNonVanillaDataCon dc tc =
       "Data constructor " ++ showOutputable dc ++
       " from type constructor " ++ showOutputable tc ++
       " is not Haskell 98!"
msgNotAlgebraicTyCon tc =
       "Type constructor " ++ showOutputable tc ++ " is not algebraic!"
msgFail s = "Internal failure: " ++ s

trTyCon :: TyCon -> TM (Datatype Id)
trTyCon tc = do
    unless (isAlgTyCon tc) (throwError (msgNotAlgebraicTyCon tc))
    dcs <- mapM tr_dc (tyConDataCons tc)
    return Datatype
        { data_ty_con = idFromTyCon tc
        , data_tvs    = map idFromTyVar tc_tvs
        , data_cons   = dcs
        }
  where
    tc_tvs = tyConTyVars tc

    tr_dc dc = do
        unless
            (isVanillaDataCon dc)
            (throwError (msgNonVanillaDataCon dc tc))
        let dc_tys = dataConInstArgTys dc (map mkTyVarTy tc_tvs)
        ts <- mapM trType dc_tys
        return Constructor
            { con_name = idFromDataCon dc
            , con_args = ts
            }

-- | Translate a definition
trDefn :: Var -> CoreExpr -> TM (Function Id)
trDefn v e = do
    let (tvs,ty) = splitForAllTys (C.exprType e)
    ty' <- trType ty
    let (tvs',body) = collectTyBinders e
    when (tvs /= tvs') (fail "Type variables do not match in type and lambda!")
    body' <- trExpr (tyAppBeta body)
    return Function
        { fn_name    = idFromVar v
        , fn_type    = Forall (map idFromTyVar tvs) ty'
        , fn_body    = body'
        }

-- | Translating variables
--
-- Need to conflate worker and wrapper data constructors otherwise
-- they might differ from case alternatives
-- (example: created tuples in partition's where clause)
-- It is unclear what disasters this might bring.
trVar :: Var -> TM (R.Expr Id)
trVar x = do
    ty <- trPolyType (varType x)
    if isLocalId x
        then case ty of
                Forall [] ti -> return (Lcl (idFromVar x) ti)
                _            -> fail ("Local identifier " ++ showOutputable x ++
                                      "with forall-type: " ++ showOutputable (varType x))
        else return $ case idDetails x of
                DataConWorkId dc -> Gbl (idFromName $ dataConName dc) ty []
                DataConWrapId dc -> Gbl (idFromName $ dataConName dc) ty []
                _                -> Gbl (idFromVar x) ty []

-- | Translating expressions
--
-- GHC Core allows application of types to arbitrary expressions,
-- but this language only allows application of types to variables.
--
-- The type variables applied to constructors in case patterns is
-- not immediately available in GHC Core, so this has to be reconstructed.
trExpr :: CoreExpr -> TM (R.Expr Id)
trExpr e0 = case e0 of
    C.Var x -> trVar x
    C.Lit (MachStr s) -> return $ String (unpackFS s)
    C.Lit l -> R.Lit <$> trLit l

    C.App e (Type t) -> do
        e' <- trExpr e
        case e' of
            R.Gbl x tx ts -> do
                t' <- trType t
                return (R.Gbl x tx (ts ++ [t']))
            _ -> throwError (msgTypeApplicationToExpr e0)

    C.App e1 e2 -> R.App <$> trExpr e1 <*> trExpr e2

    C.Lam x e -> do
        t <- trType (varType x)
        e' <- trExpr e
        return (R.Lam (idFromVar x) t e')
    -- TODO:
    --     1) Do we need to make sure x is not a type/coercion?

    C.Let bs e -> do
        bs' <- mapM (uncurry trDefn) (flattenBinds [bs])
        e' <- trExpr e
        return (R.Let bs' e')

    C.Case e x _ alts -> do

        e' <- trExpr e

        let t = C.exprType e

        t' <- trType t

        let tr_alt :: CoreAlt -> TM (R.Alt Id)
            tr_alt alt = case alt of
                (DEFAULT   ,[],rhs) -> (,) Default <$> trExpr rhs

                (DataAlt dc,bs,rhs) -> do

                    let (dc_tvs,mu) = dcAppliedTo t dc
                        unif_err    = msgUnificationError t dc_tvs dc e0

                    case mu of
                        Just u -> case mapM (lookupTyVar u) dc_tvs of
                            Just tys -> do
                                tys' <- mapM trType tys
                                bs' <- forM bs $ \ b ->
                                    (,) (idFromVar b) <$> trType (varType b)
                                rhs' <- trExpr rhs
                                dct <- trPolyType (dataConType dc)
                                return (ConPat (idFromDataCon dc {- ,dct -}) dct tys' bs',rhs')
                            Nothing -> throwError (unif_err (Just u))
                        Nothing -> throwError (unif_err Nothing)

                (LitAlt lit,[],rhs) -> do

                    -- let TyCon v [] = t'
                    lit' <- trLit lit
                    rhs' <- trExpr rhs
                    return (LitPat lit',rhs')

                _                   -> fail "Default or LitAlt with variable bindings"

        R.Case e' (Just (idFromVar x,t')) <$> mapM tr_alt alts

    C.Tick _ e -> trExpr e
    C.Type{} -> throwError (msgTypeExpr e0)
    C.Coercion{} -> throwError (msgCoercionExpr e0)
    C.Cast{} -> throwError (msgCastExpr e0)
    -- TODO:
    --     Do we need to do something about newtype casts?


-- | Translate literals. For now, the only supported literal are integers
trLit :: Literal -> TM Integer
trLit (LitInteger x _type) = return x
trLit l                    = throwError (msgUnsupportedLiteral l)

trPolyType :: C.Type -> TM (R.PolyType Id)
trPolyType t0 =
    let (tv,t) = splitForAllTys (expandTypeSynonyms t0)
    in  Forall (map idFromTyVar tv) <$> trType t

trType :: C.Type -> TM (R.Type Id)
trType = go . expandTypeSynonyms
  where
    go t0
        | Just (t1,t2) <- splitFunTy_maybe t0    = ArrTy <$> go t1 <*> go t2
        | Just (tc,ts) <- splitTyConApp_maybe t0 = TyCon (idFromTyCon tc) <$> mapM go ts
        | Just tv <- getTyVar_maybe t0           = return (TyVar (idFromTyVar tv))
        | otherwise                              = throwError (msgIllegalType t0)

