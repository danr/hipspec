{-# LANGUAGE PatternGuards #-}
-- | Translation from GHC Core to the Rich Language, a subset
module CoreToRich where

import Control.Applicative
import Control.Monad.Error

import Rich as R
import CoreSyn as C

import DataCon
import CoreUtils (exprType)
import Literal
import Var
import Name(Name)
import TyCon
import Type as C

import IdInfo

import Unify

import Utils (showOutputable)

-- | The binders in our translated expressions.
--
--   We cannot use 'Var'/'Id' because 'TyCon's do not have them,
--   and 'DataCon's does not necessarily have a unique.
--   'Name's have, just as 'Var'/'Id', a 'Unique' in them.
type Binder = Name

type TM a = Either Err a

data Err
    = UnsupportedLiteral Literal
    | IllegalType C.Type
    | TypeApplicationToExpr CoreExpr
    | TypeExpr CoreExpr
    | CoercionExpr CoreExpr
    | CastExpr CoreExpr
    | Fail String
    | UnificationError C.Type C.Type [TyVar] DataCon CoreExpr (Maybe TvSubst)

instance Show Err where
    show err = case err of
        UnsupportedLiteral l    -> "Unsupported literal: " ++ showOutputable l
        IllegalType t           -> "Illegal type: " ++ showOutputable t
        TypeApplicationToExpr e -> "Type application to expression: " ++ showOutputable e
        TypeExpr e              -> "Type expression: " ++ showOutputable e
        CoercionExpr e          -> "Coercion expression: " ++ showOutputable e
        CastExpr e              -> "Cast expression: " ++ showOutputable e
        UnificationError t1 t2 tvs dc e mu ->
            "Unification error between " ++ showOutputable t1
            ++ " and " ++ showOutputable t2
            ++ "\nWhen resolving type variables " ++ showOutputable tvs
            ++ " for constructor " ++ showOutputable dc ++
            (case mu of
                Just u -> "\nObtained unifier: " ++ showOutputable u
                Nothing -> " without unifier")
            ++ "\nOriginating from expression: " ++ showOutputable e
        Fail s -> "Internal failure: " ++ s

instance Error Err where
    strMsg = Fail

-- | Translate a definition
trDefn :: Var -> CoreExpr -> TM (Function Binder)
trDefn v e = do
    let (tvs,ty) = splitForAllTys (exprType e)
    ty' <- trType ty
    let (tvs',body) = collectTyBinders e
    when (tvs /= tvs') (fail "Type variables do not match in type and lambda!")
    body' <- trExpr body
    return Function
        { fn_name    = varName v
        , fn_ty_args = map tyVarName tvs
        , fn_type    = ty'
        , fn_body    = body'
        }

-- | Translating expressions
--
-- GHC Core allows application of types to arbitrary expressions,
-- but this language only allows application of types to variables.
--
-- The type variables applied to constructors in case patterns is
-- not immediately available in GHC Core, so this has to be reconstructed.
trExpr :: CoreExpr -> TM (R.Expr Binder)
trExpr e0 = case e0 of
    C.Var x -> (\ nm -> return (R.Var nm [])) $ case idDetails x of
        DataConWorkId dc -> dataConName dc
        DataConWrapId dc -> dataConName dc
        _                -> varName x
        -- Need to conflate worker and wrapper data constructors otherwise
        -- they might differ from case alternatives
        -- (example: created tuples in partition's where clause)
        -- It is unclear what disasters this might bring.

    C.Lit MachStr{} -> return String
    C.Lit l -> R.Lit <$> trLit l
    C.App e (Type t) -> do
        e' <- trExpr e
        case e' of
            R.Var x ts -> do
              t' <- trType t
              return (R.Var x (ts ++ [t']))
            _ -> throwError (TypeApplicationToExpr e0)
    C.App e1 e2 -> R.App <$> trExpr e1 <*> trExpr e2
    C.Lam x e -> do
        t <- trType (varType x)
        e' <- trExpr e
        t' <- trType (exprType e)
        return (R.Lam (varName x) t e' t')
    -- TODO:
    --     1) Do we need to make sure x is not a type/coercion?
    --     2) Should we save the types of the argument and body here?

    C.Let bs e -> do
        bs' <- mapM (uncurry trDefn) (flattenBinds [bs])
        e' <- trExpr e
        return (R.Let bs' e')

    C.Case e x br_ty alts -> do

        e' <- trExpr e

        br_ty' <- trType br_ty

        let t = exprType e

        let tr_alt :: CoreAlt -> TM (R.Alt Binder)
            tr_alt alt = case alt of
                (DEFAULT   ,[],rhs) -> (,) Default <$> trExpr rhs

                (DataAlt dc,bs,rhs) -> do

                    let dc_tvs = dataConUnivTyVars dc
                        res_ty = dataConOrigResTy dc
                        mu = tcUnifyTys (const BindMe) [res_ty] [t]
                        unif_err = UnificationError t res_ty dc_tvs dc e0

                    case mu of
                        Just u -> case mapM (lookupTyVar u) dc_tvs of
                            Just tys -> do
                                tys' <- mapM trType tys
                                typed_bound <- forM bs $ \ b ->
                                    (,) (varName b) <$> trType (varType b)
                                (,) (ConPat (dataConName dc) tys' typed_bound) <$> trExpr rhs
                            Nothing -> throwError (unif_err (Just u))
                        Nothing -> throwError (unif_err Nothing)

                (LitAlt lit,[],rhs) -> (,) <$> (LitPat <$> trLit lit) <*> trExpr rhs
                _                   -> fail "Default or LitAlt with variable bindings"

        R.Case e' (varName x) br_ty' <$> mapM tr_alt alts

    C.Tick _ e -> trExpr e
    C.Type{} -> throwError (TypeExpr e0)
    C.Coercion{} -> throwError (CoercionExpr e0)
    C.Cast{} -> throwError (CastExpr e0)
    -- TODO:
    --     Do we need to do something about newtype casts?

-- | Translate literals. For now, the only supported literal are integers
trLit :: Literal -> TM Integer
trLit (LitInteger x _type) = return x
trLit l                    = throwError (UnsupportedLiteral l)

trType :: C.Type -> TM (R.Type Binder)
trType t0
    | Just (t1,t2) <- splitFunTy_maybe t0    = ArrTy <$> trType t1 <*> trType t2
    | Just (tc,ts) <- splitTyConApp_maybe t0 = TyCon (tyConName tc) <$> mapM trType ts
    | Just tv <- getTyVar_maybe t0           = return (TyVar (tyVarName tv))
    | otherwise                              = throwError (IllegalType t0)

