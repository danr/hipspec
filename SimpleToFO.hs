{-# LANGUAGE ViewPatterns,DeriveFunctor,ScopedTypeVariables #-}
-- | Translating from the Simple language to the First-Order
--   language
module SimpleToFO where

import qualified Simple as S
import Simple hiding (App)
import FunctionalFO as FO
import UnPtrLocalFO

stfFun :: Ord a => S.Function (Typed a) -> FO.Function a
stfFun (S.Function (f ::: t) as b) = uplFun $
    FO.Function f tvs (map stfBndr as) res_ty (stfBody b)
  where
    (tvs,collectArrTy -> (_,res_ty)) = collectForalls t

stfBody :: Eq a => S.Body (Typed a) -> FO.Body a
stfBody b0 = case b0 of
    S.Case e alts -> FO.Case (stfExpr e) [(stfPat p,stfBody b) | (p,b) <- alts]
    S.Body e      -> FO.Body (stfExpr e)

stfPat :: forall a .Eq a => S.Pattern (Typed a) -> FO.Pattern a
stfPat p = case p of
    S.Default        -> FO.Default
    S.ConPat c ts as -> FO.ConPat (forget_type c) (map forget ts) (map stfBndr as)
    S.LitPat x _     -> FO.LitPat x

stfBndr :: Typed a -> (a,Type a)
stfBndr (x ::: t) = (x,t)

stfExpr :: Eq a => S.Expr (Typed a) -> FO.Expr a
stfExpr e0 = case e0 of
    S.Var f ts  -> Ptr (forget_type f) (map forget ts)
    S.Lit x _    -> FO.Lit x
    S.App e1 e2 -> case S.exprType e1 of
        ArrTy t1 t2 -> App t1 t2 (stfExpr e1) (stfExpr e2)
        _ -> error "SimpleToFO.stfExpr: argument not an arrow type!"

