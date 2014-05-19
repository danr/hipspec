{-# LANGUAGE ScopedTypeVariables,DeriveFunctor,FlexibleInstances,MultiParamTypeClasses #-}
-- | Translating the rich language to the simple language
--
-- Lambdas, lets an inner cases are lifted to the top level.
--
-- Free vars is calculated relative to the bound variables to not have to be
-- able to keep track of all top-level bound identifiers.
--
--   f = \ x -> g x
--
-- In the expression (g x) in this context, only x is free.
--
module HipSpec.Lang.RichToSimple where

import HipSpec.Lang.Rich as R
import HipSpec.Lang.Simple as S

import HipSpec.Lang.SimplifyRich (removeScrutinee)

import Control.Monad.RWS
import Control.Applicative

import HipSpec.Id as Id

import Data.List (nub)

type RTS = RWS
    Id              -- current derived position
    [S.Function Id] -- emitted lifted functions
    Integer         -- name supply

emit :: S.Function Id -> RTS ()
emit = tell . (:[])

runRTS :: RTS a -> (a,[S.Function Id])
runRTS m = evalRWS m (Derived Unknown 0) 0

fresh :: RTS Integer
fresh = state $ \ s -> (s,succ s)

rtsFun :: R.Function Id -> RTS (S.Function Id)
rtsFun (R.Function f ty e) = do
    let (args,body) = collectBinders e
    x <- fresh
    local (mkLetFrom f x) $ S.Function f ty (map fst args) <$> rtsBody body

rtsBody :: R.Expr Id -> RTS (S.Body Id)
rtsBody e0 = case e0 of
    R.Case e x alts -> S.Case <$> rtsExpr e <*> sequence
        [ (,) p <$> rtsBody (removeScrutinee e x alt)
        | alt@(p,_) <- alts
        ]
    _ -> S.Body <$> rtsExpr e0

rtsExpr :: R.Expr Id -> RTS (S.Expr Id)
rtsExpr e0 = case e0 of
    R.Lcl x ty     -> return (S.Lcl x ty)
    R.Gbl x ty tys -> return (S.Gbl x ty tys)
    R.App e1 e2    -> S.App <$> rtsExpr e1 <*> rtsExpr e2
    R.Lit l        -> return (S.Lit l)
    R.String s     -> error $ "rtsExpr: Found " ++ show s ++ ", but strings are not supported!"

    -- Lambda-lifting of lambda as case
    -- Emits a new function, and replaces the body with this new function
    -- applied to the type variables and free variables.
    R.Lam{}  -> emitFun Lambda e0
    R.Case{} -> emitFun Id.Case e0

    R.Let fns e -> do

        let binders = map R.fn_name fns
            free_vars =
                [ at
                | at@(a,_) <- nub (concatMap (typedFreeVars . R.fn_body) fns)
                , a `notElem` binders
                ]

        let handle_fun (R.Function _ (Forall (_:_) _) _) = error "Polymorphic let in RichToSimple!"
            handle_fun (R.Function f (Forall [] _) body) = do

                i <- fresh

                local (mkLetFrom f i) $ do

                    f' <- ask

                    let subst = (R.Gbl f' new_type (map TyVar new_ty_vars)
                                     `R.apply`
                                    map (uncurry R.Lcl) free_vars)
                            R.// f

                        fn' = R.Function f' new_type new_lambda

                    return (subst,fn')
              where
                new_lambda = makeLambda free_vars body

                new_type_body = R.exprType new_lambda

                new_ty_vars = exprTyVars new_lambda

                new_type = Forall new_ty_vars  new_type_body

        (substs,fns') <- mapAndUnzipM handle_fun fns

        -- Substitutions of the functions applied to their new arguments
        let subst :: R.Expr Id -> R.Expr Id
            subst = foldr (.) id substs

        tell =<< mapM (rtsFun . mapFnBody subst) fns'

        rtsExpr (subst e)

{-

-- These are not allowed any more, and needs to be handled in CoreToRich
-- instead

Example tricky let lifting:

    f :: forall a . a -> ([a],[a])
    f =
      \ (x :: a) ->
        let {
          g :: forall b . b -> [a]
          g = \ (y :: b) -> [] @ a
        } in (,) @ [a] @ [a]
                (g @ a x)
                (g @ [Bool] (: @ Bool True ([] @ Bool)))

This should be lifted to:

    g :: forall a b . b -> [a]
    g = \ (y :: b) -> [] @ a

    f :: forall a . a -> ([a],[a])
    f =
      \ (x :: a) ->
        (,) @ [a] @ [a]
           (g @ a @ a x)
           (g @ a @ [Bool] (: @ Bool True ([] @ Bool)))

-}

-- Emits functions for lambda and case
emitFun :: (Id -> Derived) -> R.Expr Id -> RTS (S.Expr Id)
emitFun mkName body = do

    let args       = typedFreeVars body

        new_lambda = makeLambda args body

        inner_type = R.exprType new_lambda

        ty_vars    = exprTyVars new_lambda

        new_type   = Forall ty_vars inner_type

    i <- fresh

    local (\ x -> Derived (mkName x) i) $ do

        f <- ask

        emit =<< rtsFun (R.Function f new_type new_lambda)

        return $ S.apply (S.Gbl f new_type (map TyVar ty_vars)) (map (uncurry S.Lcl) args)

