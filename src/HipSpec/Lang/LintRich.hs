{-# LANGUAGE DeriveFunctor,OverloadedStrings,RecordWildCards #-}
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
import HipSpec.Lang.PrettyUtils (Types(..),P(..))

data LintEnv v = Env
    { pp   :: P v
    , gbls :: Map v (PolyType v)
    , lcls :: Map v (Type v)
    }

withGbls :: (Map v (PolyType v) -> Map v (PolyType v)) -> LintEnv v -> LintEnv v
withGbls k e = e { gbls = k (gbls e) }

withLcls :: (Map v (Type v) -> Map v (Type v)) -> LintEnv v -> LintEnv v
withLcls k e = e { lcls = k (lcls e) }

type LintM v a = WriterT [Doc] (Reader (LintEnv v)) a

lint :: Ord v => P v -> LintM v a -> [Doc]
lint = lintWithScope []

lintWithScope :: Ord v => [(v,Type v)] -> P v -> LintM v a -> [Doc]
lintWithScope sc pk m = runReader (execWriterT m') (Env pk M.empty M.empty)
  where m' = insertLcls sc m

msgAlreadyBound :: a -> Type a -> Type a -> P a -> Doc
msgBoundAsOtherType :: a -> Type a -> Type a -> P a -> Doc
msgAlreadyBound' :: a -> PolyType a -> PolyType a -> P a -> Doc
msgBoundAsOtherType' :: a -> PolyType a -> PolyType a -> P a -> Doc
msgExprTypeDisagrees :: Expr a -> Type a -> Type a -> P a -> Doc
msgVarIncorrectlyApplied :: Expr a -> P a -> Doc
msgNotFunctionType :: Expr a -> Type a -> P a -> Doc
msgIncorrectApplication :: Expr a -> Type a -> Type a -> P a -> Doc
msgScrutineeVarIllTyped :: Expr a -> Type a -> Type a -> P a -> Doc
msgCaseWithoutAlts :: Expr a -> P a -> Doc
msgAltsRHSIllTyped :: Expr a -> [Type a] -> P a -> Doc
msgConstructorIncorrectlyApplied :: Pattern a -> P a -> Doc
msgIllTypedPattern :: Type a -> Pattern a -> P a -> Doc

msgAlreadyBound v t1 t2 pk@PK{..} = sep
       [p v,"is bound as:",ppType 0 pk t1,", but rebound as:",ppType 0 pk t2]
msgBoundAsOtherType v t1 t2 pk@PK{..} = sep
       [p v,"is bound as:",ppType 0 pk t1,", but used as:",ppType 0 pk t2]

msgAlreadyBound' v t1 t2 pk@PK{..} = sep
       [p v,"is bound as:",ppPolyType pk t1,", but rebound as:",ppPolyType pk t2]
msgBoundAsOtherType' v t1 t2 pk@PK{..} = sep
       [p v,"is bound as:",ppPolyType pk t1,", but used as:",ppPolyType pk t2]

msgExprTypeDisagrees e t1 t2 pk@PK{..} = sep
       [ppExpr' pk e,"has type:",ppType 0 pk t1,", but exprType thinks:",ppType 0 pk t2]
msgVarIncorrectlyApplied e pk@PK{..} = "Variable incorrectly applied: " <+> ppExpr' pk e
msgNotFunctionType e t pk@PK{..} = sep
       [ppExpr' pk e,"should be of function type, but is:",ppType 0 pk t]
msgIncorrectApplication e t1 t2 pk@PK{..} = sep
       [ppExpr' pk e,"incorrectly applied. Argument should be:",ppType 0 pk t1,"but is:",ppType 0 pk t2]
msgScrutineeVarIllTyped e t1 t2 pk@PK{..} = sep
       [ppExpr' pk e,"scurutinee should be:",ppType 0 pk t1,"but is:",ppType 0 pk t2]
msgCaseWithoutAlts e pk@PK{..} = "Case without alternatives: " <+> ppExpr' pk e
msgAltsRHSIllTyped e ts pk@PK{..} = sep $
       "Alternatives in case differ in type:":ppExpr' pk e:map (ppType 0 pk) ts
msgConstructorIncorrectlyApplied pat pk@PK{..} = "Constructor incorrectly applied:" <+> ppPat Show pk pat
msgIllTypedPattern t pat pk@PK{..} = ppPat Show pk pat <+> "pattern illtyped, has type:" <+> ppType 0 pk t

ppExpr' :: P a -> Expr a -> Doc
ppExpr' = ppExpr 0 Show

report :: (P v -> Doc) -> LintM v ()
report k = do
    pk <- asks pp
    tell [k pk]

insertGbl :: Ord v => (v,PolyType v) -> LintM v a -> LintM v a
insertGbl (v,t) m = do
    mt <- asks (M.lookup v . gbls)
    case mt of
        Just t' -> report (msgAlreadyBound' v t t') >> m
        Nothing -> local (withGbls (M.insert v t)) m

insertGbls :: Ord v => [(v,PolyType v)] -> LintM v a -> LintM v a
insertGbls xs m = foldr insertGbl m xs

insertLcl :: Ord v => (v,Type v) -> LintM v a -> LintM v a
insertLcl (v,t) m = do
    mt <- asks (M.lookup v . lcls)
    case mt of
        Just t' -> report (msgAlreadyBound v t t') >> m
        Nothing -> local (withLcls (M.insert v t)) m

insertLcls :: Ord v => [(v,Type v)] -> LintM v a -> LintM v a
insertLcls xs m = foldr insertLcl m xs

lintLcl :: Ord v => v -> Type v -> LintM v ()
lintLcl v t = do
    mt <- asks (M.lookup v . lcls)
    case mt of
        Just t' | not (t `eqType` t') -> report (msgBoundAsOtherType v t t')
        _ -> return ()

lintGbl :: Ord v => v -> PolyType v -> LintM v ()
lintGbl v t = do
    mt <- asks (M.lookup v . gbls)
    case mt of
        Just t' | not (t `eqPolyType` t') -> report (msgBoundAsOtherType' v t t')
        _ -> return ()

lintFns :: Ord v => [Function v] -> LintM v ()
lintFns fns = insertGbls (map ((,) <$> fn_name <*> fn_type) fns)
                              (mapM_ (lintExpr . fn_body) fns)

lintLclFnsAnd :: Ord v => [Function v] -> LintM v a -> LintM v a
lintLclFnsAnd fns m = do
    fts <- sequence
        [ case fn_type of
            Forall [] ty -> return (fn_name,ty)
            Forall __ ty -> do
                report $ \ p ->
                    ppFun Don'tShow p fn <+>
                    "is bound locally and has a polymorphic type." <+>
                    "This is not currently supported."
                return (fn_name,ty)
        | fn@Function{..} <- fns
        ]
    insertLcls fts (mapM_ (lintExpr . fn_body) fns >> m)

lintExpr :: Ord v => Expr v -> LintM v (Type v)
lintExpr e0 = chk_ret $ case e0 of
    Lcl v ty -> lintLcl v ty >> return ty
    Gbl _ (Forall tvs ty) ts -> do
        when (length ts /= length tvs) (report (msgVarIncorrectlyApplied e0))
        return (substManyTys (zip tvs ts) ty)
    App e1 e2 -> do
        t1 <- lintExpr e1
        t2 <- lintExpr e2
        case t1 of
            ArrTy ta tb -> do
                unless (ta `eqType` t2) (report (msgIncorrectApplication e0 ta t2))
                return tb
            _ -> do
                report (msgNotFunctionType e1 t1)
                return Integer
    Lit{}    -> return Integer
    String{} -> return Integer
    Lam x t e -> insertLcl (x,t) (ArrTy t <$> lintExpr e)
    Case e mx alts -> do
        ts <- lintExpr e
        case mx of
            Just (_,tx) | not (ts `eqType` tx)
                -> report (msgScrutineeVarIllTyped e0 ts tx)
            _ -> return ()
        tys <- maybe id insertLcl mx (mapM (lintAlt ts) alts)
        case tys of
            [] -> report (msgCaseWithoutAlts e0) >> return Integer
            t:tys' -> do
                unless (all (eqType t) tys') (report (msgAltsRHSIllTyped e0 tys))
                return t
    Let fns e -> lintLclFnsAnd fns (lintExpr e)
  where
    chk_ret m = do
        t <- m
        case exprType e0 of
            Nothing -> do
                report $ \ p -> ppExpr' p e0 <+> " is ill-formed wrt type!"
                return Integer
            Just t' -> do
                unless (t `eqType` t') (report (msgExprTypeDisagrees e0 t t'))
                return t

lintAlt :: Ord v => Type v -> Alt v -> LintM v (Type v)
lintAlt t0 (p,rhs) = lintPat t0 p >> lintExpr rhs

lintPat :: Ord v => Type v -> Pattern v -> LintM v ()
lintPat t0 p = case p of
    Default -> return ()
    ConPat _ (Forall tvs ty) tys args -> do
        when (length tys /= length tvs) (report (msgConstructorIncorrectlyApplied p))
        let ty' = substManyTys (zip tvs tys) ty
            (args_ty,res_ty) = collectArrTy ty'
        when (length args_ty /= length args) (report (msgConstructorIncorrectlyApplied p))
        sequence_
            [ unless (t1 `eqType` t2) (report (msgConstructorIncorrectlyApplied p))
            | ((_,t1),t2) <- zip args args_ty
            ]
        unless (res_ty `eqType` t0) (report (msgIllTypedPattern t0 p))
    LitPat{} -> unless (Integer `eqType` t0) (report (msgIllTypedPattern t0 p))

