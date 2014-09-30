{-# LANGUAGE ViewPatterns,DeriveFunctor,ScopedTypeVariables #-}
-- | Translating from the Simple language to the First-Order language
module HipSpec.Lang.SimpleToFO where

import qualified HipSpec.Lang.Simple as S
import HipSpec.Lang.Simple hiding (App)
import HipSpec.Lang.FunctionalFO as FO

import HipSpec.Id

stfFun :: S.Function Id -> FO.Function Id
stfFun (S.Function f (Forall tvs ty) as b) =
    FO.Function f tvs (zip as arg_tys) res_ty (fmap stfBody b)
  where
    peel 0 t            = ([],t)
    peel n (ArrTy ta t) = let (tas,r) = peel (n - 1) t in (ta:tas,r)
    peel _ _            = error "SimpleToFO.peel: not an arrow type!"

    (arg_tys,res_ty)    = peel (length as) ty

stfBody :: S.Body Id -> FO.Body Id
stfBody b0 = case b0 of
    S.Case e alts -> FO.Case (stfExpr e) [ (stfPat p,stfBody b) | (p,b) <- alts ]
    S.Body e      -> FO.Body (stfExpr e)

stfPat :: S.Pattern Id -> FO.Pattern Id
stfPat p = case p of
    S.Default            -> FO.Default
    S.ConPat c _ty ts as -> FO.ConPat c ts as
    S.LitPat x           -> FO.LitPat x

stfExpr :: S.Expr Id -> FO.Expr Id
stfExpr e0 = case e0 of
    S.Lcl f _ty     -> Fun f [] []
    S.Gbl f _ty tys -> Ptr f tys
    S.Lit x         -> FO.Lit x
    S.App e1 e2 -> case S.exprType e1 of
        ArrTy t1 t2 -> App t1 t2 (stfExpr e1) (stfExpr e2)
        _           -> error "SimpleToFO.stfExpr: argument not an arrow type!"

