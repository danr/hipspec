{-# LANGUAGE PatternGuards, PackageImports #-}

-- | Translation from GHC Core to the Rich Language, a subset
module Lang.CoreToRich where

import Control.Applicative
import Control.Monad.Error

import Lang.Rich as R
import Lang.Type as R

import CoreUtils as C
import CoreSyn as C

import DataCon
import Literal
import Var
import Name(Name)
import TyCon hiding (data_cons)
import Type as C
import GHC (dataConType)

import Lang.DataConPattern

import IdInfo

import Lang.Utils (showOutputable)

import Lang.TyAppBeta

-- | The binders in our translated expressions.
--
--   We cannot use 'Var'/'Id' because 'TyCon's do not have them,
--   and 'DataCon's does not necessarily have a unique.
--   'Name's have, just as 'Var'/'Id', a 'Unique' in them.
--
--   The types need to be remembered so we used typed
type Binder = Typed Name

type TM a = Either Err a

data Err
    = UnsupportedLiteral Literal
    | IllegalType C.Type
    | TypeApplicationToExpr CoreExpr
    | TypeExpr CoreExpr
    | CoercionExpr CoreExpr
    | CastExpr CoreExpr
    | Fail String
    | HigherRankType Var C.Type
    | UnificationError C.Type [TyVar] DataCon CoreExpr (Maybe TvSubst)
    | NonVanillaDataCon DataCon TyCon
    | NotAlgebraicTyCon TyCon

instance Show Err where
    show err = case err of
        UnsupportedLiteral l    -> "Unsupported literal: " ++ showOutputable l
        IllegalType t           -> "Illegal type: " ++ showOutputable t
        TypeApplicationToExpr e -> "Type application to expression: " ++ showOutputable e
        TypeExpr e              -> "Type expression: " ++ showOutputable e
        CoercionExpr e          -> "Coercion expression: " ++ showOutputable e
        CastExpr e              -> "Cast expression: " ++ showOutputable e
        HigherRankType v t      -> showOutputable v ++ " has a higher-rank type: " ++ showOutputable t
        UnificationError t tvs dc e mu ->
            "Unification error on " ++ showOutputable t
            ++ "\nWhen resolving type variables " ++ showOutputable tvs
            ++ " for constructor " ++ showOutputable dc ++
            (case mu of
                Just u -> "\nObtained unifier: " ++ showOutputable u
                Nothing -> " without unifier")
            ++ "\nOriginating from expression: " ++ showOutputable e
        NonVanillaDataCon dc tc ->
            "Data constructor " ++ showOutputable dc ++
            " from type constructor " ++ showOutputable tc ++
            " is not Haskell 98!"
        NotAlgebraicTyCon tc ->
            "Type constructor " ++ showOutputable tc ++ " is not algebraic!"
        Fail s -> "Internal failure: " ++ s

instance Error Err where
    strMsg = Fail

trTyCon :: TyCon -> TM (Datatype Name)
trTyCon tc = do
    unless (isAlgTyCon tc) (throwError (NotAlgebraicTyCon tc))
    dcs <- mapM tr_dc (tyConDataCons tc)
    return Datatype
        { data_ty_con = tyConName tc
        , data_tvs    = map tyVarName tc_tvs
        , data_cons   = dcs
        }
  where
    tc_tvs = tyConTyVars tc

    tr_dc dc = do
        unless
            (isVanillaDataCon dc)
            (throwError (NonVanillaDataCon dc tc))
        let dc_tys = dataConInstArgTys dc (map mkTyVarTy tc_tvs)
        ts <- mapM trType dc_tys
        return Constructor
            { con_name = dataConName dc
            , con_args = ts
            }

-- | Translate a definition
trDefn :: Var -> CoreExpr -> TM (Function Binder)
trDefn v e = do
    let (tvs,ty) = splitForAllTys (C.exprType e)
    ty' <- trType ty
    let (tvs',body) = collectTyBinders e
    when (tvs /= tvs') (fail "Type variables do not match in type and lambda!")
    body' <- trExpr (tyAppBeta body)
    let tvs_named = map tyVarName tvs
    return Function
        { fn_name    = varName v ::: makeForalls tvs_named ty'
        , fn_body    = body'
        }

-- | Translating variables
--
-- Need to conflate worker and wrapper data constructors otherwise
-- they might differ from case alternatives
-- (example: created tuples in partition's where clause)
-- It is unclear what disasters this might bring.
trVar :: Var -> TM Binder
trVar x = do
    ty <- trType (varType x)
    return . (::: ty) $ case idDetails x of
        DataConWorkId dc -> dataConName dc
        DataConWrapId dc -> dataConName dc
        _                -> varName x

-- | Translating expressions
--
-- GHC Core allows application of types to arbitrary expressions,
-- but this language only allows application of types to variables.
--
-- The type variables applied to constructors in case patterns is
-- not immediately available in GHC Core, so this has to be reconstructed.
trExpr :: CoreExpr -> TM (R.Expr Binder)
trExpr e0 = case e0 of
    C.Var x -> (`R.Var` []) <$> trVar x
    C.Lit MachStr{} -> String <$> star e0_ty_con
    C.Lit l -> R.Lit <$> trLit l <*> star e0_ty_con

    C.App e (Type t) -> do
        e' <- trExpr e
        case e' of
            R.Var x ts -> do
                t' <- star <$> trType t
                return (R.Var x (ts ++ [t']))
            _ -> throwError (TypeApplicationToExpr e0)

    C.App e1 e2 -> R.App <$> trExpr e1 <*> trExpr e2

    C.Lam x e -> do
        assertNotForAllTy x
        t <- trType (varType x)
        e' <- trExpr e
        return (R.Lam (varName x ::: t) e')
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

        let tr_alt :: CoreAlt -> TM (R.Alt Binder)
            tr_alt alt = case alt of
                (DEFAULT   ,[],rhs) -> (,) Default <$> trExpr rhs

                (DataAlt dc,bs,rhs) -> do

                    mapM_ assertNotForAllTy bs

                    let (dc_tvs,mu) = dcAppliedTo t dc
                        unif_err    = UnificationError t dc_tvs dc e0

                    case mu of
                        Just u -> case mapM (lookupTyVar u) dc_tvs of
                            Just tys -> do
                                tys' <- mapM (fmap star . trType) tys
                                bs' <- forM bs $ \ b ->
                                    (varName b :::) <$> trType (varType b)
                                rhs' <- trExpr rhs
                                dct <- trType (dataConType dc)
                                return (ConPat (dataConName dc ::: dct) tys' bs',rhs')
                            Nothing -> throwError (unif_err (Just u))
                        Nothing -> throwError (unif_err Nothing)

                (LitAlt lit,[],rhs) -> do

                    let TyCon v [] = t'
                    lit' <- trLit lit
                    rhs' <- trExpr rhs
                    return (LitPat lit' (v ::: Star),rhs')

                _                   -> fail "Default or LitAlt with variable bindings"

        R.Case e' (Just (varName x ::: t')) <$> mapM tr_alt alts

    C.Tick _ e -> trExpr e
    C.Type{} -> throwError (TypeExpr e0)
    C.Coercion{} -> throwError (CoercionExpr e0)
    C.Cast{} -> throwError (CastExpr e0)
    -- TODO:
    --     Do we need to do something about newtype casts?
  where
    e0_ty_con = do
        t <- trType (C.exprType e0)
        case t of
            TyCon x [] -> return x
            _          -> fail "Literal is not of a type constructor type!"


-- | Translate literals. For now, the only supported literal are integers
trLit :: Literal -> TM Integer
trLit (LitInteger x _type) = return x
trLit l                    = throwError (UnsupportedLiteral l)

trType :: C.Type -> TM (R.Type Name)
trType = go . expandTypeSynonyms
  where
    go t0
        | Just (t1,t2) <- splitFunTy_maybe t0    = ArrTy <$> go t1 <*> go t2
        | Just (tc,ts) <- splitTyConApp_maybe t0 = TyCon (tyConName tc) <$> mapM go ts
        | Just (tv,t) <- splitForAllTy_maybe t0  = Forall (tyVarName tv) <$> go t
        | Just tv <- getTyVar_maybe t0           = return (TyVar (tyVarName tv))
        | otherwise                              = throwError (IllegalType t0)

assertNotForAllTy :: Var -> TM ()
assertNotForAllTy v = when (isForAllTy t) (throwError (HigherRankType v t))
  where t = varType v

