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

import Data.List (nub)

data Rename a
    = Old a   -- an old name
    | New Int -- a fresh name
  deriving (Eq,Ord,Show)

type RTS v = RWS (Map (Rename v) (Type (Rename v))) -- types of variables in scope
                 [Function (Rename v)]              -- emitted lifted functions
                 (State Int)                        -- name supply

emit :: Function (Rename v) -> RTS v ()
emit = tell . (:[])

runRTS :: RTS v a -> (a,[Function (Rename v)])
runRTS m = evalRWS m M.empty 0

fresh :: RTS v (Rename v)
fresh = state $ \ s -> (New s,succ s)

typeOf :: Ord v => Rename v -> RTS v (Type (Rename v))
typeOf x = do
    m <- ask
    case M.lookup x m of
        Just ty -> return ty
        Nothing -> error "Identifier escaped!"

extendScope1 :: Ord v => Rename v -> Type (Rename v) -> RTS v a -> RTS v a
extendScope1 x t = insertTypes [(x,t)]

extendScope :: Ord v => [(Rename v,Type (Rename v))] -> RTS v a -> RTS v a
extendScope xsts = local $ M.union (M.toList xsts)

clearScope :: RTS v a -> RTS v a
clearScope = local $ const M.empty

rtsFun :: Ord v => R.Function (Rename v) -> RTS v (S.Function (Rename v))
rtsFun (R.Function f tvs t e) = do
    let (typed_args,body) = collectBinders e
    clearScope $ extendScope typed_args $
        S.Function f tvs t (map fst typed_args) <$> rtsBody body

rtsBody :: Ord v => R.Expr (Rename v) -> RTS v (S.Body (Rename v))
rtsBody (R.Case e x alts) = S.Case (rtsExpr e) <$> sequence
    [ (,) p <$> rtsBody (removeScrutinee e x rhs)
      -- insert types of bound constructor variabels!
    | (p,rhs) <- alts
    ]
rtsBody e = S.Body <$> rtsExpr e

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
            free_vars         = R.freeVars e0
        typed_free_vars <- sequence [ (,) v <$> typeOf v | v <- free_vars ]
        f <- fresh
        let (new_lambda,new_type)
                = makeLambda (typed_free_vars ++ typed_args) body body_type
            ty_vars
                = nub (concatMap R.freeTyVars (body_type ++ map snd typed_args))
        emit =<< rtsFun (R.Function f ty_vars body_type new_lambda)
        return (S.apply (S.Var f (map S.TyVar ty_vars)) free_vars)

-- TODO: Types of constructor types... Put this in the Rich AST or make an environment?
