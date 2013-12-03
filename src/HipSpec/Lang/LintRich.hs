{-# LANGUAGE DeriveFunctor,OverloadedStrings #-}
module HipSpec.Lang.LintRich where

import HipSpec.Lang.Rich
import HipSpec.Lang.Type

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as M

import Text.PrettyPrint
import HipSpec.Lang.PrettyRich

type LintM v a = WriterT [Err v] (Reader (v -> Doc,Map v (Type v))) a

lint :: Ord v => LintM v a -> [Err v]
lint = lintWithScope []

lintWithScope :: Ord v => [(v,Type v)] -> LintM v a -> [Err v]
lintWithScope sc m = runReader (execWriterT m') M.empty
  where m' = insertVars sc m

msgAlreadyBound v t1 t2 p = sep
       [p v,"is bound as:",ppType 0 p t1,", but rebound as:",ppType 0 p t2]
msgBoundAsOtherType v t1 t2 p = sep
       [p v,"is bound as:",ppType 0 p t1,", but used as:",ppType 0 p t2]
msgExprTypeDisagrees e t1 t2 p = sep
       [ppExpr 0 p e,"has type:",ppType 0 p t1,", but exprType thinks:",ppType 0 p t2]
msgVarIncorrectlyApplied e p = "Variable incorrectly applied: " <+> ppExpr 0 p e
msgNotFunctionType e t p = sep
       [ppExpr 0 p e,"should be of function type, but is:",ppType 0 p t]
msgIncorrectApplication e t1 t2 p = sep
       [ppExpr 0 p e,"incorrectly applied. Argument should be:",ppType 0 p t1,"but is:",ppType 0 p t2]
msgScrutineeVarIllTyped e t1 t2 p = sep
       [ppExpr 0 p e,"scurutinee should be:",ppType 0 p t1,"but is:",ppType 0 p t2]
msgCaseWithoutAlts e p = "Case without alternatives: " <+> ppExpr 0 p e
msgAltsRHSIllTyped e ts p = sep $
       "Alternatives in case differ in type:":ppExpr 0 p e:map (ppType 0 p) ts
msgConstructorIncorrectlyApplied pat p = "Constructor incorrectly applied:" <+> ppPat p pat
msgIllTypedPattern t pat p = ppPat p pat <+> "pattern illtyped, has type:" <+> ppType 0 p t

report :: ((v -> Doc) -> Doc) -> LintM v ()
report k = do
    p <- asks fst
    tell [k p]

insertVar :: Ord v => (v,Type v) -> LintM v a -> LintM v a
insertVar (v,t) m = do
    mt <- asks (M.lookup v . snd)
    case mt of
        Just t' -> report (AlreadyBound v t t') >> m
        Nothing -> local (M.insert v t) m

insertVars :: Ord v => [(v,Type v)] -> LintM v a -> LintM v a
insertVars xs m = foldr insertVar m xs

lintVar :: Ord v => v -> Type v -> LintM v ()
lintVar v t = do
    mt <- asks (M.lookup v . snd)
    case mt of
        Just t' | not (t `eqType` t') -> report (BoundAsOtherType v t t')
        _ -> return ()

lintFns :: Ord v => [Function (Typed v)] -> LintM v ()
lintFns fns = lintFnsAnd fns (return ())

lintFnsAnd :: Ord v => [Function (Typed v)] -> LintM v a -> LintM v a
lintFnsAnd fns m = insertVars (map fn_name fns)
                              (mapM_ (lintExpr . fn_body) fns >> m)

lintExpr :: Ord v => Expr v -> LintM v (Type v)
lintExpr e0 = chk_ret $ case e0 of
    Lcl v ty -> do
        lintVar v ty
    Var v@(_ ::: ty) ts -> do
        lintVar v
        let (tvs,ty') = collectForalls ty
        when (length ts /= length tvs) (report (VarIncorrectlyApplied e0))
        return (substManyTys (zip tvs (map forget ts)) ty')
    App e1 e2 -> do
        t1 <- lintExpr e1
        t2 <- lintExpr e2
        case t1 of
            ArrTy ta tb -> do
                unless (ta `eqType` t2) (report (IncorrectApplication e0 ta t2))
                return tb
            _ -> do
                report (NotFunctionType e1 t1)
                return Star
    Lit _ (t ::: _) -> return (TyCon t [])
    String (t ::: _) -> return (TyCon t [])
    Lam x@(_ ::: t) e -> insertVar x (ArrTy t <$> lintExpr e)
    Case e mx {- @(_ ::: tx) -} alts -> do
        ts <- lintExpr e
        case mx of
            Just (_ ::: tx) | not (ts `eqType` tx)
                -> report (ScrutineeVarIllTyped e0 ts tx)
            _ -> return ()
        tys <- maybe id insertVar mx (mapM (lintAlt ts) alts)
        case tys of
            [] -> report (CaseWithoutAlts e0) >> return Star
            t:tys' -> do
                unless (all (eqType t) tys') (report (AltsRHSIllTyped e0 tys))
                return t
    Let fns e -> lintFnsAnd fns (lintExpr e)
  where
    chk_ret m = do
        t <- m
        let t' = exprType e0
        unless (t `eqType` t') (report (ExprTypeDisagrees e0 t t'))
        return t

lintAlt :: Ord v => Type v -> Alt (Typed v) -> LintM v (Type v)
lintAlt t0 (p,rhs) = lintPat t0 p >> lintExpr rhs

lintPat :: Ord v => Type v -> Pattern (Typed v) -> LintM v ()
lintPat t0 p = case p of
    Default -> return ()
    ConPat (_ ::: t) tys args -> do
        let (tvs,ty) = collectForalls t
        when (length tys /= length tvs) (report (ConstructorIncorrectlyApplied p))
        let ty' = substManyTys (zip tvs (map forget tys)) ty
            (args_ty,res_ty) = collectArrTy ty'
        when (length args_ty /= length args) (report (ConstructorIncorrectlyApplied p))
        sequence_
            [ unless (t1 `eqType` t2) (report (ConstructorIncorrectlyApplied p))
            | (_ ::: t1,t2) <- zip args args_ty
            ]
        unless (res_ty `eqType` t0) (report (IllTypedPattern t0 p))
    LitPat _ (t ::: _) -> when (TyCon t [] /= t0) (report (IllTypedPattern t0 p))

