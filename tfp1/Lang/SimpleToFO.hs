{-# LANGUAGE ViewPatterns,DeriveFunctor,ScopedTypeVariables #-}
-- | Translating from the Simple language to the First-Order language
--
--   The scope needs to be kept track of to not make pointers to the bound
--   variables.
module Lang.SimpleToFO where

import Control.Monad.Reader
import Control.Applicative

import qualified Lang.Simple as S
import Lang.Simple hiding (App)
import Lang.FunctionalFO as FO

import Lang.Scope

type STF v a = Reader (Scope v) a

runSTF :: STF v a -> a
runSTF m = runReader m emptyScope

runSTFWithScope :: Ord v => [v] -> STF v a -> a
runSTFWithScope s m = runReader m (makeScope s)

stfFun :: Ord v => S.Function (Typed v) -> FO.Function v
stfFun (S.Function (f ::: ty) as b) =
    FO.Function f tvs as' res_ty $ runSTF $
    extendScope (map fst as') (stfBody b)
  where
    as' = map stfBndr as

    peel 0 t           = t
    peel n (ArrTy _ t) = peel (n - 1) t
    peel _ _           = error "SimpleToFO.peel: not an arrow type!"

    (tvs,ty') = collectForalls ty
    res_ty    = peel (length as) ty'

stfBody :: Ord v => S.Body (Typed v) -> STF v (FO.Body v)
stfBody b0 = case b0 of
    S.Case e alts -> FO.Case <$> stfExpr e <*> sequence
                        [ (,) p' <$> scopePat p' (stfBody b)
                        | (p,b) <- alts
                        , let p' = stfPat p
                        ]
    S.Body e      -> FO.Body <$> stfExpr e

stfPat :: Ord v => S.Pattern (Typed v) -> FO.Pattern v
stfPat p = case p of
    S.Default        -> FO.Default
    S.ConPat c ts as -> FO.ConPat (forget_type c) (map forget ts) (map stfBndr as)
    S.LitPat x _     -> FO.LitPat x

scopePat :: Ord v => FO.Pattern v -> STF v a -> STF v a
scopePat p = case p of
    FO.ConPat _ _ as -> extendScope (map fst as)
    _                -> id

stfBndr :: Typed v -> (v,Type v)
stfBndr (x ::: t) = (x,t)

stfExpr :: Ord v => S.Expr (Typed v) -> STF v (FO.Expr v)
stfExpr e0 = case e0 of
    S.Var f ts  -> do
        let f'  = forget_type f
            ts' = map forget ts
        b <- inScope f'
        return $ if b then chk_null ts' (Fun f' ts' []) else Ptr f' ts'
      where
        chk_null [] = id
        chk_null _  = error "SimpleToFO.stfExpr: Variable applied to types!"
    S.Lit x _   -> return (FO.Lit x)
    S.App e1 e2 -> case S.exprType e1 of
        ArrTy t1 t2 -> App t1 t2 <$> stfExpr e1 <*> stfExpr e2
        _ -> error "SimpleToFO.stfExpr: argument not an arrow type!"

