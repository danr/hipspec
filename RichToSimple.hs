{-# LANGUAGE ScopedTypeVariables,DeriveFunctor #-}
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
module RichToSimple where

import Rich as R
import Simple as S

import SimplifyRich (removeScrutinee)

import Data.Set (Set)
import qualified Data.Set as S

import Control.Monad.RWS
import Control.Applicative

import Data.List (nub,(\\))

type Var a = Typed (Rename a)

data Rename a
    = Old a   -- an old name
    | New Int -- a fresh name
  deriving (Eq,Ord,Show,Functor)

type RTS v = RWS
    (Set (Var v))        -- variables in scope
    [S.Function (Var v)] -- emitted lifted functions
    Int                  -- name supply

emit :: S.Function (Var v) -> RTS v ()
emit = tell . (:[])

runRTS :: RTS v a -> (a,[S.Function (Var v)])
runRTS m = evalRWS m S.empty 0

fresh :: Type (Rename v) -> RTS v (Var v)
fresh t = state $ \ s -> (New s ::: t,succ s)

extendScope :: Ord v => [Var v] -> RTS v a -> RTS v a
extendScope = local . S.union . S.fromList

clearScope :: RTS v a -> RTS v a
clearScope = local (const S.empty)

rtsFun :: Ord v => R.Function (Var v) -> RTS v (S.Function (Var v))
rtsFun (R.Function f e) = do
    let (args,body) = collectBinders e
    clearScope $ extendScope args $
        S.Function f args <$> rtsBody body

rtsBody :: Ord v => R.Expr (Var v) -> RTS v (S.Body (Var v))
rtsBody e0 = case e0 of
    R.Case e x alts -> S.Case <$> rtsExpr e <*> sequence
        [ (,) p <$> bindPattern p (rtsBody (removeScrutinee e x alt))
        | alt@(p,_) <- alts
        ]
    _ -> S.Body <$> rtsExpr e0
  where
    bindPattern p = case p of
        ConPat _ _ bs -> extendScope bs
        _             -> id

rtsExpr :: forall v . Ord v => R.Expr (Var v) -> RTS v (S.Expr (Var v))
rtsExpr e0 = case e0 of
    R.Var x ts  -> return (S.Var x ts)
    R.App e1 e2 -> S.App <$> rtsExpr e1 <*> rtsExpr e2
    R.Lit l t   -> return (S.Lit l t)
    R.String{}  -> error "rtsExpr: Strings are not supported!"

    -- Lambda-lifting
    -- Emits a new function, and replaces the lambda
    -- with this new function applied to the type variables and free variables.
    R.Lam{} -> do
        let (args,body) = R.collectBinders e0
        free_vars <- exprFreeVars e0
        emitFun (free_vars ++ args) body

    R.Case{} -> do
        free_vars <- exprFreeVars e0
        emitFun free_vars e0

    R.Let fns e -> do
        -- See Example tricky let lifting

        let binders = map R.fn_name fns
            free_vars_overapprox
                = nub (concatMap (R.freeVars . R.fn_body) fns) \\ binders

        free_vars <- freeVarsOf free_vars_overapprox

        let handle_fun (R.Function fn@(f ::: ft) body) = (subst,fn')
              where
                (tvs,_) = collectForalls ft

                new_lambda = makeLambda free_vars body

                new_type_body = R.exprType new_lambda

                new_ty_vars = freeTyVars new_type_body \\ tvs

                new_type = makeForalls (new_ty_vars ++ tvs) new_type

                f' = f ::: new_type

                subst = tySubst fn $ \ ty_args ->
                    R.Var f' (map (star . TyVar) new_ty_vars ++ ty_args)
                    `R.apply`
                    map (`R.Var` []) free_vars

                fn' = R.Function f' new_lambda

            (substs,fns') = unzip (map handle_fun fns)

        -- Substitutions of the functions applied to their new arguments
        let subst :: R.Expr (Var v) -> R.Expr (Var v)
            subst = foldr (.) id substs

        tell =<< mapM (rtsFun . mapFnBody subst) fns'

        rtsExpr (subst e)

{-

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

emitFun :: forall v . Ord v => [Var v] -> R.Expr (Var v) -> RTS v (S.Expr (Var v))
emitFun args body = do

    let new_lambda = makeLambda args body

        new_type   = R.exprType new_lambda

        ty_vars    = freeTyVars new_type

    f <- fresh (makeForalls ty_vars new_type)

    emit =<< rtsFun (R.Function f new_lambda)

    return (S.apply (S.Var f (map (star . S.TyVar) ty_vars))
                    (map (`S.Var` []) args))

-- | Gets the free vars of an expression
exprFreeVars :: Ord v => R.Expr (Var v) -> RTS v [Var v]
exprFreeVars = freeVarsOf . R.freeVars

-- | Given a list of variables, gets the free variables and their types
freeVarsOf :: Ord v => [Var v] -> RTS v [Var v]
freeVarsOf = filterM (asks . S.member)

typeVarsOf :: Ord v => Type v -> [v]
typeVarsOf = nub . freeTyVars

