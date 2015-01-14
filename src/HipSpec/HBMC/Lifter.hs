{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs #-}
module HipSpec.HBMC.Lifter (liftFunction, liftFunction_trace) where

import HipSpec.HBMC.Utils
-- import qualified Data.Foldable as F

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import HipSpec.Utils

import Data.Maybe
import Control.Monad.State hiding (lift)

-- Transforms
--    case e of brs
-- to
--    let x = e in case x of brs
caseOnVars :: TransformBiM Fresh (Expr Id) t => t -> Fresh t
caseOnVars = transformBiM tr
  where
    tr e0 = case e0 of
        Case Lcl{} _        _   -> return e0
        Case e (Just (x,t)) brs -> return $ Let [Function x (q t) e] (Case (Lcl x t) Nothing brs)
        Case e Nothing      brs -> do
            let t = exprType' "caseOnVars" e
            x <- newCaser
            tr (Case e (Just (x,t)) brs)
        _ -> return e0

{-

    case x of
        K1 x1 -> C1[e]
        K2 x2 -> C2[e]
        K3 x3 -> C3

    is transformed to

    combine e var
        (case x of
            K1 x1 -> fst (fromJust (tmpl e))
            K2 x2 -> fst (fromJust (tmpl e))
            K3 x3 -> def)
        (case x of
            K1 x1 -> C1[snd (fromJust (tmpl e)) (Lcl var)]
            K2 x2 -> C2[snd (fromJust (tmpl e)) (Lcl var)]
            K3 x3 -> C3)

    Future optimisation: save values bound by lets from the first argument
    to the second argument to avoid recomputation.
    This could be done in a separate pass

-}
lifter :: forall a . (Eq a,a ~ Id) => Fresh a
       -> (Expr a -> Maybe (Expr a,(Expr a -> Expr a,Type a))) -> Expr a
       -> ([Expr a] -> a -> Expr a -> Expr a -> Expr a)
       -> Expr a -> Fresh (Expr a)
lifter var tmpl def combine = go
  where
    go :: Expr a -> Fresh (Expr a)
    go e | not (findExpr (isJust . tmpl) e) = return e

    go (Case a mx brs) | length (filter (findExpr (isJust . tmpl) . snd) brs) <= 1 = do
        brs' <- mapM (\ (p,e) -> do e' <- go e; return (p,e')) brs
        return (Case a mx brs')

    go e0@(Let [Function _f _t b] _e)
        | findExpr (isJust . tmpl) b
        = error $ "Case on recursive call not supported yet: " ++ showRexpr e0
{-
        b' <- go b
        return (Let [Function f t b'] e)
        -}

    go (Let fns e) = Let fns <$> go e

    -- always lift, since we create new variable names as arguments and use
    -- this as termination criterion (!)
    go c = do
        let repl tmpl_proj handle_arm = replaceTop (fmap tmpl_proj . tmpl) handle_arm c
        x <- var
        let (before,ess) = repl fst (\ _ e -> case e of Just e' -> e'; Nothing -> def)
        let (after,_)    = repl (\ (_,(k,xt)) -> k (Lcl x xt)) (\ a _ -> a)
        return (combine ess x before after)

commonAll :: Integer -> Id -> [Type Id] -> Expr Id -> Fresh (Expr Id)
commonAll s0 f arg_tys = lifter newArg tmpl (noop t) (\ _ -> mkLet)
  where
    n = length arg_tys

    t = TyCon (hid $ TupleTyCon n) arg_tys

    tmpl e = case collectArgs e of
        (fg@(Gbl g _ _),args)
            | g == f
            , length arg_tys == length args
            , not (any (argOk (< s0)) args)
            , not (any (findExpr (isJust . tmpl)) args)
            -> Just
                ( tuple args
                , ( \ x -> fg `apply` [ Gbl (hid $ Select n j) (selectType n j) arg_tys `App` x | j <- [0..n-1] ]
                                        -- if you change the line above, also change argOk!
                  , t
                  )
                )
        _ -> Nothing

-- We have already processed arguments that are (peek (projX argZ)) if p Z
argOk :: (Integer -> Bool) -> Expr Id -> Bool
argOk p e = case e of
    Gbl{} `App` arg -> argExprSat p arg
    _ -> False

expensive :: (Expr Id -> Bool) -> Expr Id -> Fresh (Expr Id)
expensive p = lifter
    newRes
    (\ e -> if p e then Just (ghcTrue,(id,exprType' "expensive" e)) else Nothing)
    ghcFalse
    (\ ess x tf e -> case ess of
        a:as | any (/= a) as -> error "different expensive"
        [] -> error "empty expensive"
        a:_ -> mkLet x (ite tf a (noop (exprType' "expensive" a))) e)

replaceTop :: (a ~ Id) => (Expr a -> Maybe (Expr a)) -> (Expr a -> Maybe (Expr a) -> Expr a) -> Expr a -> (Expr a,[Expr a])
replaceTop tmpl handle_arm = go
  where
    go e0 = case e0 of
        Let fns e ->
            let (e',ess) = go e
            in  (Let fns e',ess)

        Case e mx brs ->
            let (brs',ess) = unzip [ ((p,br'),es) | (p,br) <- brs, let (br',es) = go br ]
            in  (Case e mx brs',concat ess)
        e ->
            let (e',me) = replaceFirst tmpl e
            in  (handle_arm e' (fmap snd me),maybeToList (fmap fst me))

replaceFirst :: (TransformBiM (State (Maybe (Expr a,Expr a))) (Expr a) t,a ~ Id,t ~ Expr Id)
             => (Expr a -> Maybe (Expr a)) -> t -> (t,Maybe (Expr a,Expr a))
replaceFirst tmpl e0 = (`runState` Nothing) . transformBiM tr $ e0
  where
    tr e = do
        replaced <- get
        case (e,replaced,tmpl e) of
            (Case{},_      ,_) -> error $ "Case must be on top level (for now):\n" ++ showRexpr e0
            (Lam{} ,_      ,_) -> error "Lambda must be on top level (for now)"
            (_     ,Just{} ,_) -> return e
            (orig  ,Nothing,Just r)  -> put (Just (orig,r)) >> return r
            (_     ,Nothing,Nothing) -> return e

liftFunction :: Function Id -> Fresh (Function Id)
liftFunction = fmap last . liftFunction_trace

liftFunction_trace :: Function Id -> Fresh [Function Id]
liftFunction_trace (Function f pty@(Forall _tvs (collectArrTy -> (arg_tys,_res_ty))) b0)
    = fmap wrap . go =<< (caseOnVars `underLambda` b0)
  where
    wrap xs = [Function f pty b | b <- b0:xs ]

    continue = findExpr $ \ e -> case collectArgs e of
        (Gbl g _ _,args) | f == g, length args >= length arg_tys -> any (not . argOk (const True)) args
        _ -> False

    go :: Expr Id -> Fresh [Expr Id]
    go b | continue b = do

        s0 <- get

        b' <-  commonAll s0 f arg_tys `underLambda` b

        let new_f e = case collectArgs e of
                (Gbl g _ _,args) ->
                    g == f && length args == length arg_tys && all (argOk (>= s0)) args
                _ -> False

        b_unopt <- expensive new_f `underLambda` b'

        let b_res = simpExpr' False b_unopt

        res <- go b_res

        return (b:b':b_unopt:res)

    go b = return [b]

