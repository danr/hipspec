-- Transforms the program to prolog monadic form.
--
-- Assumes all function calls are perfectly saturated.
--
-- Ignores and destroys typing (!)
--
-- Has an environment to understand when a function is pure, and slaps on
-- an extra return after calling it.
{-# LANGUAGE PatternGuards,ViewPatterns #-}
module HipSpec.HBMC.Prolog (monadic,runMon,monExpr,Mon,IdType(..)) where

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

runMon :: Mon a -> (Maybe Id -> Id -> IdType) -> Fresh a
runMon m f = runReaderT m (Nothing,f)

data IdType = IsCon | IsRec | IsOk

type Mon = ReaderT (Maybe Id, Maybe Id -> Id -> IdType) Fresh

monadic :: Function Id -> Mon (Function Id)
monadic (Function f _t (collectBinders -> (args,body))) =
  do res <- lift newRes
     body' <- local (first (const (Just f))) (monExpr (lcl res) body)
     return (Function f unpty (makeLambda (args ++ [(res,unty)]) body'))

trivial :: Expr Id -> Bool
trivial Lcl{} = True
trivial _     = False

monExpr :: Expr Id -> Expr Id -> Mon (Expr Id)
monExpr res e0 =
  case collectArgs e0 of
    -- function call
    (Gbl x _ _,args) ->
      do (cur_fn,id_type_fn) <- ask
         let id_type = id_type_fn cur_fn x
         case id_type of
           IsCon | any (not . trivial) args ->
             do xs <- mapM (\ _ -> lift (newTmp "x")) args
                es <- zipWithM (monExpr . lcl) xs args
                return $
                  gbl (isCon x)
                    `apply`
                       [ res
                       , makeLambda
                           [ (x,unty) | x <- xs ]
                           (case es of
                             [] -> noop (error "noop type") `App` res
                             _  -> inSequence (init es) (last es)
                           )
                       ]
           _ ->
             do let f args = case id_type of
                       _ | x == noopId -> gbl x `apply` args
                       IsCon -> gbl (predCon x) `apply` args
                       IsRec -> gbl postpone `App` (gbl x `apply` args)
                       IsOk  -> gbl x `apply` args
                makeNews (length args) $
                  \ xs ->
                    do es <- zipWithM monExpr xs args
                       return (inSequence es (f (xs ++ [res])))

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
             alts' <- mapM (monAlt res) alts
             return (tr1 >>> Case z Nothing alts')

    -- Lam x _ e  -> Lam x unty <$> monExpr e

    x -> error $ "monExpr: not implemented yet:\n" ++ ppShow x

monAlt :: Expr Id -> Alt Id -> Mon (Alt Id)
monAlt res (ConPat k pty ts ys,e) =
  do body <- monExpr res e
     return (ConPat k pty ts ys,body)


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

