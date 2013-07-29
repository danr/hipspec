{-# LANGUAGE DeriveFunctor,OverloadedStrings #-}
module Lang.LintRich where

import Lang.Rich
import Lang.Type

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as M

import Text.PrettyPrint
import Lang.PrettyRich

type LintM v a = WriterT [Err v] (Reader (Map v (Type v))) a

lint :: Ord v => LintM v a -> [Err v]
lint m = runReader (execWriterT m) M.empty

type TypedExpr v = Expr (Typed v)

data Err v
    = AlreadyBound v (Type v) (Type v)
    | BoundAsOtherType v (Type v) (Type v)
    | ExprTypeDisagrees (TypedExpr v) (Type v) (Type v)
    | VarIncorrectlyApplied (TypedExpr v)
    | NotFunctionType (TypedExpr v) (Type v)
    | IncorrectApplication (TypedExpr v) (Type v) (Type v)
    | ScrutineeVarIllTyped (TypedExpr v) (Type v) (Type v)
    | CaseWithoutAlts (TypedExpr v)
    | AltsRHSIllTyped (TypedExpr v) [Type v]
    | ConstructorIncorrectlyApplied (Pattern (Typed v))
    | IllTypedPattern (Type v) (Pattern (Typed v))
  deriving (Show,Functor)

ppErr :: (v -> Doc) -> Err v -> Doc
ppErr p err = case err of
    AlreadyBound v t1 t2 -> sep
        [p v,"is bound as:",ppType 0 p t1,", but rebound as:",ppType 0 p t2]
    BoundAsOtherType v t1 t2 -> sep
        [p v,"is bound as:",ppType 0 p t1,", but used as:",ppType 0 p t2]
    ExprTypeDisagrees e t1 t2 -> sep
        [ppExpr 0 k e,"has type:",ppType 0 p t1,", but exprType thinks:",ppType 0 p t2]
    VarIncorrectlyApplied e -> "Variable incorrectly applied: " <+> ppExpr 0 k e
    NotFunctionType e t -> sep
        [ppExpr 0 k e,"should be of function type, but is:",ppType 0 p t]
    IncorrectApplication e t1 t2 -> sep
        [ppExpr 0 k e,"incorrectly applied. Argument should be:",ppType 0 p t1,"but is:",ppType 0 p t2]
    ScrutineeVarIllTyped e t1 t2 -> sep
        [ppExpr 0 k e,"scurutinee should be:",ppType 0 p t1,"but is:",ppType 0 p t2]
    CaseWithoutAlts e -> "Case without alternatives: " <+> ppExpr 0 k e
    AltsRHSIllTyped e ts -> sep $
        "Alternatives in case differ in type:":ppExpr 0 k e:map (ppType 0 p) ts
    ConstructorIncorrectlyApplied pat -> "Constructor incorrectly applied:" <+> ppPat k pat
    IllTypedPattern t pat -> ppPat k pat <+> "pattern illtyped, has type:" <+> ppType 0 p t
  where
    k = (p . forget_type,ppTyped p)

report :: Err v -> LintM v ()
report = tell . (:[])

insertVar :: Ord v => Typed v -> LintM v a -> LintM v a
insertVar (v ::: t) m = do
    mt <- asks (M.lookup v)
    case mt of
        Just t' -> report (AlreadyBound v t t') >> m
        Nothing -> local (M.insert v t) m

insertVars :: Ord v => [Typed v] -> LintM v a -> LintM v a
insertVars xs m = foldr insertVar m xs

lintVar :: Ord v => Typed v -> LintM v ()
lintVar (v ::: t) = do
    mt <- asks (M.lookup v)
    case mt of
        Just t' | not (t `eqType` t') -> report (BoundAsOtherType v t t')
        _ -> return ()

lintFns :: Ord v => [Function (Typed v)] -> LintM v ()
lintFns fns = lintFnsAnd fns (return ())

lintFnsAnd :: Ord v => [Function (Typed v)] -> LintM v a -> LintM v a
lintFnsAnd fns m = insertVars (map fn_name fns)
                              (mapM_ (lintExpr . fn_body) fns >> m)

lintExpr :: Ord v => TypedExpr v -> LintM v (Type v)
lintExpr e0 = chk_ret $ case e0 of
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

