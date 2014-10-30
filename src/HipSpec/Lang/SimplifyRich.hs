{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, ExplicitForAll #-}
-- | Simplify pass over the rich language:
--
--  * Inlines local non-recursive definitions,
--  * Eliminates known-case:
--      - when the scrutinee expression is a constructor
--      - by inlining/eliminating the scrutinee variable
--  * Beta reduction
--
-- These passes destroy sharing and make the program less efficient.
-- However, they should preserve the semantics (even in presence of
-- non-terminating programs/bottoms)
--
-- TODO: Inline non-recursive global definitions
--       Polymorphic lets
module HipSpec.Lang.SimplifyRich where

import HipSpec.Lang.Rich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import TysWiredIn (trueDataCon,falseDataCon,boolTyCon,nilDataCon,consDataCon)
import DataCon (dataConWorkId)
import PrimOp (PrimOp(TagToEnumOp))
import PrelNames (unpackCStringName)
import Data.Char (ord)
import HipSpec.Lang.CoreToRich as CTR
import TysWiredIn

unpackStrings :: TransformBi (Expr Id) t => t -> t
unpackStrings = transformBi $ \ e0 -> case e0 of
    App (Gbl (GHCOrigin x) _ _) (String s)
        | x == unpackCStringName ->
            foldr (\ x xs -> apply cons [apply mkChar [Lit (toInteger (ord x))],xs]) nil s
    _ -> e0
  where
    Right (onChar -> nil)  = CTR.runTM (CTR.trVar (dataConWorkId nilDataCon))
    Right (onChar -> cons) = CTR.runTM (CTR.trVar (dataConWorkId consDataCon))
    Right mkChar           = CTR.runTM (CTR.trVar (dataConWorkId charDataCon))

onChar (Gbl a t []) = Gbl a t [TyCon (idFromTyCon charTyCon) []]

integerToInt :: TransformBi (Expr Id) t => t -> t
integerToInt = transformBi $ \ e0 -> case e0 of
    Gbl (GHCOrigin x) ty [] | Just op <- convertIntegerToInt x -> Gbl (GHCPrim op) ty []
    _ -> e0

unTagToEnum :: TransformBi (Expr Id) t => t -> t
unTagToEnum = transformBi $ \ e0 -> case e0 of
    App (Gbl (GHCPrim TagToEnumOp) _ty_tte [_int])
        (collectArgs -> (Gbl (GHCPrim x) _ty_op _tys,args))
      | Just op <- convertPrim x
        -> App (Gbl FromProverBool (q fromProverBoolType) [])
               (Gbl (OtherPrim op) (q (otherPrimOpType op)) [] `apply` args)
    _ -> e0

fromProverBoolDefn :: Function Id
fromProverBoolDefn = Function f (q ty)
    (Lam x proverBoolType
        (Case (Lcl x proverBoolType) Nothing
            [ (ConPat true  (q proverBoolType) [] [],Gbl (idFromDataCon trueDataCon)  (q boolType) [])
            , (ConPat false (q proverBoolType) [] [],Gbl (idFromDataCon falseDataCon) (q boolType) [])
            ]))
  where
    f  = FromProverBool
    ty = fromProverBoolType
    x  = Lambda f `Derived` 0
    true  = OtherPrim ProverTrue
    false = OtherPrim ProverFalse

fromProverBoolType :: Type Id
fromProverBoolType = proverBoolType `ArrTy` boolType

q :: Type a -> PolyType a
q = Forall []

etaExpand :: Function Id -> Function Id
etaExpand
    (Function f ty@(Forall tvs (collectArrTy -> (arg_tys,body_ty)))
                   (collectBinders -> (args,body)))
    = Function f ty new_body
  where
    args'    = (map fst args ++ [ Lambda f `Derived` i | i <- [0..] ]) `zip` arg_tys
    new_args = drop (length args) args'
    new_body = makeLambda args' (apply body (map (uncurry Lcl) new_args))


simpFuns :: Eq a => [Function a] -> [Function a]
simpFuns = map (simpFun Global)

data Where = Global | Local deriving Eq

simpFun :: Eq a => Where -> Function a -> Function a
simpFun loc (Function f ty b) = Function f ty $ simpExpr $ case b of
    -- Sometimes functions look like this
    -- f = \ xs -> let g = K[g] in g,
    -- then we simply replace it to f = \ xs -> K[f xs]
    -- TODO: Polymorphic functions (find examples!)

    (collectBinders -> (xs,Let [Function g (Forall [] _) e] (Lcl g' _)))
        | g == g'
        , Forall tvs inner_ty <- ty
        , null tvs || loc == Global ->
            let
                var = case loc of
                    Global -> Gbl
                    Local  -> \ a _ _ -> Lcl a inner_ty
            in
                makeLambda xs
                   ((var f ty (map TyVar tvs) `apply` map (uncurry Lcl) xs // g) e)

    _ -> b

simpExpr :: Eq a => Expr a -> Expr a
simpExpr = transformExpr $ \ e0 -> case e0 of

    -- Beta reduction
    App (Lam x _ body) arg -> simpExpr ((arg // x) body)

    -- Known case on a constructor
    Case e mx alts
        | (Gbl u _ ts,args) <- collectArgs e
        , Just (ConPat _ _ _ bs,rhs) <- findAlt u ts alts
        -> simpExpr (substMany (maybe id (\ (x,_) -> ((x,e):)) mx (zip (map fst bs) args)) rhs)

    Case e mx [(Default,rhs)] -> substMany (maybe [] (\ (x,_) -> [(x,e)]) mx) rhs

    Case (Let fns e) x alts -> simpExpr (Let fns (Case e x alts))

    Case e x alts -> Case e Nothing
                        [ (p,simpExpr (removeScrutinee e x alt))
                        | alt@(p,_) <- alts
                        ]

    -- Inlining local non-recursive functions
    -- TODO: Handle several functions, handle polymorphic functions (no examples yet)
    -- Cannot inline this to several occasions if e contains a let
    Let [Function f (Forall [] _) b] e
        | not (f `occursIn` b)
        , letFree b {- || occurrences f e <= 1 -} -> simpExpr ((b // f) e)


    Let fns e -> Let (map (simpFun Local) fns) (simpExpr e)

    _ -> e0

-- | Removes the scrutinee variable (and also the expression if it is a variable),
--   by inlining the pattern or the expression again (if it is a Default alt)
removeScrutinee :: Eq a => Expr a -> Maybe (a,Type a) -> Alt a -> Expr a
removeScrutinee e mx (p,rhs) = subst rhs
  where
    subst_expr  = case p of
        Default           -> e
        LitPat l          -> Lit l
        ConPat u ty ts bs -> apply (Gbl u ty ts) (map (uncurry Lcl) bs)

    -- If the scrutinee is just a variable, we inline it too.
    -- This can lead to triggering many known case.
    subst = substMany . (`zip` repeat subst_expr) . maybe id ((:) . fst) mx $ case e of
        Lcl u _ -> [u] -- The variable can only be locally bound by lambda
                       -- or case and thus is not applied to type args.
        _       -> []

