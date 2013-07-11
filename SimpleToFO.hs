{-# LANGUAGE ViewPatterns,DeriveFunctor,ScopedTypeVariables #-}
-- | Translating from the Simple language to the First-Order
--   language
module SimpleToFO where

import qualified Simple as S
import Simple hiding (App)
import FunctionalFO as FO
import UnPtrLocalFO

stfFun :: Ord a => S.Function (Typed a) -> FO.Function (Var a)
stfFun (S.Function f as b) = uplFun $
    FO.Function (stfVar f) (map stfPtr as) (stfBody b)

stfVar :: Eq a => Typed a -> Var a
stfVar (v S.::: t) = Orig v FO.::: fmap Orig (trTy t)
  where
    trTy :: Type a -> FOType a
    trTy (collectForalls -> (ts,collectArrTy -> (arg,res))) = FOType ts arg res


stfBody :: Eq a => S.Body (Typed a) -> FO.Body (Var a)
stfBody b0 = case b0 of
    S.Case e alts -> FO.Case (stfExpr e) [(stfPat p,stfBody b) | (p,b) <- alts]
    S.Body e      -> FO.Body (stfExpr e)

stfPat :: forall a .Eq a => S.Pattern (Typed a) -> FO.Pattern (Var a)
stfPat p = case p of
    S.Default        -> FO.Default
    S.ConPat c ts as -> FO.ConPat (stfVar c) (map (stfType . forget) ts) (map stfPtr as)

    S.LitPat x tc    -> FO.LitPat x (stfVar tc)

app :: Var a
app = App FO.::: FOType [X,Y] [ArrTy x y,x] y
  where [x,y] = map TyVar [X,Y]

stfPtr :: Typed a -> Var a
stfPtr (v S.::: (collectForalls . fmap Orig -> (ts,t))) = Ptr v FO.::: FOType ts [] t

stfExpr :: Eq a => S.Expr (Typed a) -> FO.Expr (Var a)
stfExpr e0 = case e0 of
    S.Var f ts  -> Apply (stfPtr f) (map (stfType . forget) ts) []
    S.App e1 e2 -> case S.exprType e1 of
        ArrTy t1 t2 ->
            Apply app [stfType t1,stfType t2] [stfExpr e1,stfExpr e2]
        _ -> error "stfExpr: argument not an arrow type!"
    S.Lit x tc -> FO.Lit x (stfVar tc)

stfType :: Type a -> Type (Var a)
stfType = fmap (\ t -> Orig t FO.::: FOType [] [] Star)

