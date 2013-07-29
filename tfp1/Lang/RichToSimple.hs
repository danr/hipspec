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
module Lang.RichToSimple where

import Lang.Rich as R
import Lang.Simple as S

import Lang.SimplifyRich (removeScrutinee)

import Lang.Scope

import Control.Monad.RWS
import Control.Applicative

import Data.List (nub,(\\))

type Var a = Typed (Rename a)

data Rename a
    = Old a                        -- an old name
    | New [Loc (Rename a)] Integer -- a fresh name
  deriving (Eq,Ord,Show,Functor)

data Loc a = CaseLoc | LamLoc | LetLoc a
  deriving (Eq,Ord,Show,Functor)

newtype Env v = Env (Scope v,[Loc v])

instance HasScope v (Env v) where
    get_scope (Env (s,_))   = get_scope s
    mod_scope f (Env (s,a)) = Env (mod_scope f s,a)

type RTS v = RWS
    (Env (Var v))        -- variables in scope
    [S.Function (Var v)] -- emitted lifted functions
    Integer              -- name supply

emit :: S.Function (Var v) -> RTS v ()
emit = tell . (:[])

runRTS :: Ord v => RTS v a -> (a,[S.Function (Var v)])
runRTS = runRTSWithScope [] []

runRTSWithScope :: Ord v =>
    [Loc (Rename v)] -> [Var v] -> RTS v a -> (a,[S.Function (Var v)])
runRTSWithScope loc sc m = evalRWS m (Env (makeScope sc,map star loc)) 0

getLocs :: forall v . RTS v [Loc (Rename v)]
getLocs = do
    Env (_,ls) <- ask
    let ls' :: [Loc (Rename v)]
        ls' = [ forget l | l <- ls ]
    return ls'

withNewLoc :: Loc (Rename v) -> RTS v a -> RTS v a
withNewLoc l = local $ \ (Env (sc,ls)) -> Env (sc,ls ++ [star l])

fresh :: Type (Rename v) -> RTS v (Var v)
fresh t = do
    ls <- getLocs
    state $ \ s -> (New ls s ::: t,succ s)

rtsFun :: Ord v => R.Function (Var v) -> RTS v (S.Function (Var v))
rtsFun (R.Function f e) = do
    let (args,body) = collectBinders e
    withNewLoc (LetLoc (forget_type f)) $ clearScope $ extendScope args $
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

    -- Lambda-lifting of lambda as case
    -- Emits a new function, and replaces the body with this new function
    -- applied to the type variables and free variables.
    R.Lam{}  -> emitFun LamLoc e0
    R.Case{} -> emitFun CaseLoc e0

    R.Let fns e -> do
        -- See Example tricky let lifting

        let binders = map R.fn_name fns
            free_vars_overapprox
                = nub (concatMap (R.freeVars . R.fn_body) fns) \\ binders

        free_vars <- freeVarsOf free_vars_overapprox

        let handle_fun (R.Function fn@(f ::: ft) body) = withNewLoc (LetLoc f) $ do

                f' <- fresh new_type

                let subst = tySubst fn $ \ ty_args ->
                        R.Var f' (map (star . TyVar) new_ty_vars ++ ty_args)
                        `R.apply`
                        map (`R.Var` []) free_vars

                    fn' = R.Function f' new_lambda

                return (subst,fn')
              where
                (tvs,_) = collectForalls ft

                new_lambda = makeLambda free_vars body

                new_type_body = R.exprType new_lambda

                new_ty_vars = freeTyVars new_type_body \\ tvs

                new_type = makeForalls (new_ty_vars ++ tvs) new_type_body

        (substs,fns') <- mapAndUnzipM handle_fun fns

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

emitFun :: forall v . Ord v => Loc (Rename v) -> R.Expr (Var v) -> RTS v (S.Expr (Var v))
emitFun l body = do

    args <- exprFreeVars body

    let new_lambda = makeLambda args body

        new_type   = R.exprType new_lambda

        ty_vars    = freeTyVars new_type

    withNewLoc l $ do

        f <- fresh (makeForalls ty_vars new_type)

        emit =<< rtsFun (R.Function f new_lambda)

        return (S.apply (S.Var f (map (star . S.TyVar) ty_vars))
                        (map (`S.Var` []) args))

-- | Gets the free vars of an expression
exprFreeVars :: Ord v => R.Expr (Var v) -> RTS v [Var v]
exprFreeVars = freeVarsOf . R.freeVars

-- | Given a list of variables, gets the free variables and their types
freeVarsOf :: Ord v => [Var v] -> RTS v [Var v]
freeVarsOf = pluckScoped

typeVarsOf :: Ord v => Type v -> [v]
typeVarsOf = nub . freeTyVars

