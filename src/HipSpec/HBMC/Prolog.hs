-- Transforms the program to prolog monadic form.
--
-- Assumes all function calls are perfectly saturated.
--
-- Ignores and destroys typing (!)
--
-- Has an environment to understand when a function is pure, and slaps on
-- an extra return after calling it.
{-# LANGUAGE PatternGuards,ViewPatterns #-}
module HipSpec.HBMC.Prolog (monadic,runMon,monExpr,Mon) where

import HipSpec.HBMC.Utils hiding (lift)

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import HipSpec.Utils

import Data.Generics.Geniplate

import Control.Monad.Reader

import Data.Maybe (listToMaybe)

runMon = runReaderT

type Mon = ReaderT (Id -> Int -> Bool) Fresh

monadic :: Function Id -> Mon (Function Id)
monadic (Function f _t (collectBinders -> (args,body))) =
  do res <- lift newRes
     body' <- monExpr (lcl res) body
     return (Function f unpty (makeLambda (args ++ [(res,unty)]) body'))

monExpr :: Expr Id -> Expr Id -> Mon (Expr Id)
monExpr res e0 =
  case collectArgs e0 of
    -- function call
    (Gbl x _ _,args) ->
      makeNews (length args) $
        \ xs ->
          do es <- zipWithM monExpr xs args
             return (inSequence es (gbl x `apply` (xs ++ [res])))
         -- pure?

    -- base cases
    (Lcl x _, []) -> return (e0 === res)
    (Lit{},   []) -> return (e0 === res)
    (String{},[]) -> return (e0 === res)

    -- lets
    (Let [] e,[]) -> monExpr res e
    (Let (Function f _ b:fns) e,[]) ->
      makeNew False $
        \ f_copy ->
          (>>>)
            <$> monExpr f_copy b
            <*> monExpr res ((f_copy // f) (Let fns e))

    -- case
    (Case s mx alts,[]) ->
      makeNew True $
        \ z ->
          do tr1 <- monExpr z s
             choices <- mapM (monAlt z res) alts
             return (tr1 >>> (gbl choice `App` listLit choices))

    -- Lam x _ e  -> Lam x unty <$> monExpr e

    x -> error $ "monExpr: " ++ show x ++ " not implemented yet"

monAlt :: Expr Id -> Expr Id -> Alt Id -> Mon (Expr Id)
monAlt ms res (ConPat k _ _ ys,e) =
  do body <- monExpr res e
     return (gbl (isCon k) `apply` [ms,makeLambda ys body])

makeNew :: Bool -> (Expr Id -> Mon (Expr Id)) -> Mon (Expr Id)
makeNew inline k =
  do x <- lift newArg
     e <- k (lcl x)
     case isEqual x e of
       Just e' | inline -> return (rmRefl $ (e' // x) e)
       _ -> lift (bind x (gbl new) e)

isEqual :: Id -> Expr Id -> Maybe (Expr Id)
isEqual x e0 = listToMaybe $
    [ e
    | Gbl f _ _ `App` Lcl x' _ `App` e <- universe e0
    , f == equalHere
    , x' == x
    ] ++
    [ e
    | Gbl f _ _ `App` e `App` Lcl x' _ <- universe e0
    , f == equalHere
    , x' == x
    ]

-- equalHere x x >> m = m
rmRefl :: Expr Id -> Expr Id
rmRefl = transformBi $
  \ stmts ->
    case stmts of
      StmtExpr (Gbl f _ _ `App` Lcl x _ `App` Lcl y _):m
        | f == equalHere
        , x == y
        -> m
      _ -> stmts

makeNews :: Int -> ([Expr Id] -> Mon (Expr Id)) -> Mon (Expr Id)
makeNews 0 k = k []
makeNews n k = makeNew True $ \ x -> makeNews (n-1) $ \ xs -> k (x:xs)


{-
bindExpr :: Expr Id -> (Expr Id -> Mon (Expr Id)) -> Mon (Expr Id)
bindExpr e k = do
    e' <- monExpr x e
    x <- lift tmp
    e'' <- k (Lcl x unty)
    lift (bind e' (Lam x unty e''))

bindExprs :: [Expr Id] -> ([Expr Id] -> Mon (Expr Id)) -> Mon (Expr Id)
bindExprs []     k = k []
bindExprs (e:es) k = bindExpr e $ \ x -> bindExprs es $ \ xs -> k (x:xs)
-}

