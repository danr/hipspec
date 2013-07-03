{-# LANGUAGE ScopedTypeVariables,DeriveFunctor #-}
-- | Translating the rich language to the simple language
--
-- Lambdas, lets an inner cases are lifted to the top level.
module RichToSimple where

import Rich as R
import Simple as S

import SimplifyRich (removeScrutinee)

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad.RWS
import Control.Applicative

import Data.List (nub,(\\))

data Rename a
    = Old a   -- an old name
    | New Int -- a fresh name
  deriving (Eq,Ord,Show,Functor)

type RTS v = RWS (Map (Rename v) (Type (Rename v))) -- types of variables in scope
                 [S.Function (Rename v)]            -- emitted lifted functions
                 Int                                -- name supply

emit :: S.Function (Rename v) -> RTS v ()
emit = tell . (:[])

runRTS :: RTS v a -> (a,[S.Function (Rename v)])
runRTS m = evalRWS m M.empty 0

fresh :: RTS v (Rename v)
fresh = state $ \ s -> (New s,succ s)

typeOf :: Ord v => Rename v -> RTS v (Type (Rename v))
typeOf x = do
    m <- ask
    case M.lookup x m of
        Just ty -> return ty
        Nothing -> error "Identifier escaped!"

extendScope :: Ord v => [(Rename v,Type (Rename v))] -> RTS v a -> RTS v a
extendScope xsts = local $ M.union (M.fromList xsts)

clearScope :: RTS v a -> RTS v a
clearScope = local $ const M.empty

rtsFun :: Ord v => R.Function (Rename v) -> RTS v (S.Function (Rename v))
rtsFun (R.Function f tvs t e) = do
    let (typed_args,body) = collectBinders e
    clearScope $ extendScope typed_args $
        S.Function f tvs t (map fst typed_args) <$> rtsBody body

rtsBody :: Ord v => R.Expr (Rename v) -> RTS v (S.Body (Rename v))
rtsBody e0 = case e0 of
    R.Case e x _ alts -> S.Case <$> rtsExpr e <*> sequence
        [ (,) p <$> bindPattern p (rtsBody (removeScrutinee e x alt))
        | alt@(p,_) <- alts
        ]
    _ -> S.Body <$> rtsExpr e0
  where
    bindPattern p = case p of
        ConPat _ _ typed_bound -> extendScope typed_bound
        _                      -> id

rtsExpr :: Ord v => R.Expr (Rename v) -> RTS v (S.Expr (Rename v))
rtsExpr e0 = case e0 of
    R.Var x ts  -> return (S.Var x ts)
    R.App e1 e2 -> S.App <$> rtsExpr e1 <*> rtsExpr e2
    R.Lit l     -> return (S.Lit l)
    R.String    -> error "rtsExpr: Strings are not supported!"

    -- Lambda-lifting
    -- Emits a new function, and replaces the lambda
    -- with this new function applied to the type variables and free variables.
    R.Lam _ _ b t -> do
        let (typed_args,body) = R.collectBinders e0
            body_type         = R.lambdaBodyType t b
        typed_free_vars <- typedFreeVars e0
        emitFun (typed_free_vars ++ typed_args) body body_type

    R.Case _ _ t _ -> do
        typed_free_vars <- typedFreeVars e0
        emitFun typed_free_vars e0 t

    R.Let fns e -> do
        -- See Example tricky let lifting
        let rhs (R.Function _ _ _ b) = b
        typed_free_vars <- nub . concat <$> mapM (typedFreeVars . rhs) fns
        -- ^ TODO: Need a proper free vars for functions!!! errors here!
        let free_vars = map fst typed_free_vars

        substs <- forM fns $ \ (R.Function f tvs body_type body) -> do
            let (new_lambda,new_type) = makeLambda typed_free_vars body body_type
                new_ty_vars = typeVarsOf (body_type:map snd typed_free_vars) \\ tvs
            emit =<< rtsFun (R.Function f (new_ty_vars ++ tvs) new_type new_lambda)
            return $ tySubst f $ \ ty_args ->
                R.apply (R.Var f (map R.TyVar new_ty_vars ++ ty_args))
                        (map (`R.Var` []) free_vars)

        rtsExpr (foldr (.) id substs e)

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

emitFun :: Ord v => [(Rename v,Type (Rename v))] -> R.Expr (Rename v) -> Type (Rename v)
           -> RTS v (S.Expr (Rename v))
emitFun typed_args body body_type = do
    f <- fresh
    let args = map fst typed_args
        (new_lambda,new_type) = makeLambda typed_args body body_type
        ty_vars = typeVarsOf (body_type:map snd typed_args)
    emit =<< rtsFun (R.Function f ty_vars new_type new_lambda)
    return (S.apply (S.Var f (map S.TyVar ty_vars))
                    (map (`S.Var` []) args))

   {-

        forM fns $ \ (Function fn tvs body_type body) ->
            -- Need to get the /new/ type variables that are not in tvs.
            -- They need to be pre-applied
            let args = map fst typed_free_vars
                (new_lambda,new_type) = makeLambda typed_args body body_type
                ty_vars = typeVarsOf (map snd typed_args) \\ tvs
            emit =<< rtsFun (R.Function f ty_vars body_type new_lambda)
            return (S.apply (S.Var f (map S.TyVar ty_vars)) typed_args)

emitFunWithNameAndTyVars :: Rename v -> [Rename v] -> [(Rename v,Type (Rename v))] -> Expr (Rename v) -> Type (Rename v) -> RTS v (S.Expr (Rename v))
emitFunWithNameAndTyVars f tvs typed_args body body_type = do
    let args = map fst typed_args
        (new_lambda,new_type) = makeLambda typed_args body body_type
        ty_vars = typeVarsOf (body_type ++ map snd typed_args)
    emit =<< rtsFun (R.Function f (ty_vars body_type new_lambda)
    return (S.apply (S.Var f (map S.TyVar ty_vars)) typed_args)

emitFun :: [(Rename v,Type (Rename v))] -> Expr (Rename v) -> Type (Rename v) -> RTS v (S.Expr (Rename v))
emitFun a e t = do
    f <- fresh
    emitFunWithNameAndTyVars f [] a e t
    -}

typedFreeVars :: Ord v => R.Expr (Rename v) -> RTS v [(Rename v,Type (Rename v))]
typedFreeVars e = sequence [ (,) v <$> typeOf v | v <- R.freeVars e ]

typeVarsOf :: Ord v => [Type (Rename v)] -> [Rename v]
typeVarsOf = nub . concatMap R.freeTyVars

-- TODO: Types of constructor types... Put this in the Rich AST or make an environment?
