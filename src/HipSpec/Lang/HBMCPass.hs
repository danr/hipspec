{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs #-}
module HipSpec.Lang.HBMCPass where

-- import qualified Data.Foldable as F

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import HipSpec.Utils

import Data.Maybe
import Control.Monad.State

type Fresh = State Integer

fresh :: Fresh Integer
fresh = state (\ s -> (s,succ s))

newArg :: Fresh Id
newArg = Derived Arg <$> fresh

newRes :: Fresh Id
newRes = Derived Res <$> fresh

newCaser :: Fresh Id
newCaser = Derived Caser <$> fresh

unr :: Type Id -> Expr Id
unr t = Gbl UNR (Forall [x] (TyCon Lift [TyVar x])) [t]
  where
    x = LiftTV

the :: Expr Id -> Expr Id
the e = Gbl The (Forall [x] (TyVar x `ArrTy` TyCon Lift [TyVar x])) [t] `App` e
  where
    x = LiftTV
    t = exprType' "the" e

peek :: Expr Id -> Expr Id
peek e = Gbl Peek (Forall [x] (TyCon Lift [TyVar x] `ArrTy` TyVar x)) [t] `App` e
  where
    x = LiftTV
    t = case exprType' "peek" e of
        TyCon Lift [t] -> t
        t' -> error $ "peek on " ++ ppShow e ++ " with type " ++ ppShow t'

-- Transforms
--    case e of brs
-- to
--    let x = e in case x of brs
caseOnVars :: TransformBiM Fresh (Expr Id) t => t -> Fresh t
caseOnVars = transformBiM tr
  where
    tr e0 = case e0 of
        Case Lcl{} _        brs -> return e0
        Case e (Just (x,t)) brs -> return $ Let [Function x (q t) e] (Case (Lcl x t) Nothing brs)
        Case e Nothing      brs -> do
            let t = exprType' "caseOnVars" e
            x <- newCaser
            tr (Case e (Just (x,t)) brs)
        _ -> return e0

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

{-
    go (Let [Function f t b] e) | findExpr (isJust . tmpl) b = do
        b' <- go b
        return (Let [Function f t b'] e)
        -}

    go (Let fns e) = Let fns <$> go e

    -- always lift, since we create new variable names as arguments
    go c = do
        let repl u v = replaceTop (fmap u . tmpl) v c
        x <- var
        let (before,ess) = repl fst (\ _ e -> case e of Just e' -> e'; Nothing -> def)
        let (after,_)    = repl (\ (_,(k,xt)) -> k (Lcl x xt)) (\ a _ -> a)
        return (combine ess x before after)

common :: Expr Id -> Type Id -> Expr Id -> Fresh (Expr Id)
common f arg_ty = lifter
    newArg
    (\ e0 -> case e0 of
        App g x | f == g && not (findExpr (== f) x) -> Just (the x,(\ e -> App g e,exprType' "common" x))
        _ -> Nothing)
    (unr arg_ty)
    (\ _ -> mkLet)

commonLong :: Integer -> Id -> [Type Id] -> Expr Id -> Fresh (Expr Id)
commonLong s0 f arg_tys e0 = foldM
    (\ e i -> do
        let tmpl a = case collectArgs a of
                (fg@(Gbl g _ _),args)
                    | g == f
                    , length arg_tys == length args
                    , not (any (argExprSat (< s0)) args)
                    , not (any (findExpr (isJust . tmpl)) args)
                    -> Just
                        ( the (args !! i)
                        , ( \ x -> apply fg (replaceAt args i x)
                          , arg_tys !! i
                          )
                        )
                _ -> Nothing
        lifter newArg tmpl (unr (arg_tys !! i)) (\ _ -> mkLet) e)
    e0
    [0..length arg_tys-1]

replaceAt :: [a] -> Int -> a -> [a]
replaceAt xs i x = case splitAt i xs of
    (l,_:r) -> l ++ [x] ++ r
    _       -> error "replaceAt"

{-
commonLong :: Integer -> Id -> [Type Id] -> Expr Id -> Fresh (Expr Id)
commonLong s0 f arg_tys e0 = fst <$> foldM
    (\ (e,tmpl) arg_ty -> do
        let tmpl' a = case a of
                App g x
                    | Just{} <- tmpl g
                    , not (argExprSat (< s0) x) -- not already lifted
--                    , not (findExpr (isJust . tmpl) x)
                    -> Just (the x,(App g,exprType' "commonLong" x))
                _ -> Nothing
        e' <- lifter newArg tmpl' (unr arg_ty) (\ _ -> mkLet) e
        return (e',tmpl')
    )
    ( e0
    , \ a -> case a of
        Gbl g _ _ | g == f -> Just (error "commonLong: init")
        _                  -> Nothing
    )
    arg_tys
    -}

expensive :: (Expr Id -> Bool) -> Expr Id -> Fresh (Expr Id)
expensive p = lifter
    newRes
    (\ e -> if p e then Just (ghcTrue,(peek,TyCon Lift [exprType' "expensive" e])) else Nothing)
    ghcFalse
    (\ ess x tf e -> case ess of
        a:as | any (/= a) as -> error "different expensive"
        [] -> error "empty expensive"
        a:_ -> mkLet x (ite tf (the a) (unr (exprType' "expensive" a))) e)

mkLet :: Eq a => a -> Expr a -> Expr a -> Expr a
mkLet x ls e = Let [Function x (q (exprType' "mkLet" ls)) ls] e

ite :: Expr Id -> Expr Id -> Expr Id -> Expr Id
ite e t f = Case e Nothing [(pat ghcTrueId,t),(pat ghcFalseId,f)]
  where
    pat i = ConPat i (q boolType) [] []

findExpr :: (Expr a -> Bool) -> Expr a -> Bool
findExpr p = any p . universe

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

underLambda :: Functor m => (Expr a -> m (Expr a)) -> Expr a -> m (Expr a)
underLambda k b = makeLambda xs `fmap` k e
  where (xs,e) = collectBinders b

argSat :: (Integer -> Bool) -> Id -> Bool
argSat p (Derived Arg i) = p i
argSat _ _               = False

argId :: Id -> Bool
argId = argSat (const True)

argExpr :: Expr Id -> Bool
argExpr (Lcl i _) = argId i
argExpr _         = False

argExprSat :: (Integer -> Bool) -> Expr Id -> Bool
argExprSat p (Lcl i _) = argSat p i
argExprSat _ _         = False

resExpr :: Expr Id -> Bool
resExpr (Lcl (Derived Res _) _) = True
resExpr _                       = False

hbmc :: Function Id -> Fresh [Function Id]
hbmc (Function f pty@(Forall tvs (collectArrTy -> (arg_tys,_res_ty))) b0)
    = fmap ret . go =<< (caseOnVars `underLambda` b0)

{-
        b' <- caseOnVars `underLambda` b
        b'' <- common (Gbl f pty (map TyVar tvs)) ty_arg `underLambda` b'
    _ -> return []
    -}
  where
    ret xs = [Function f pty b | b <- b0:xs ]

    continue = findExpr $ \ e -> case collectArgs e of
        (Gbl g _ _,args) | f == g, length args >= length arg_tys -> any (not . argExpr) args
        _ -> False

    go :: Expr Id -> Fresh [Expr Id]
    go b | continue b = do

        s0 <- get

        b' <- commonLong s0 f arg_tys `underLambda` b

        let new_f e = case collectArgs e of
                (Gbl f _ _,args) ->
                    length args == length arg_tys && all (argExprSat (>= s0)) args
                _ -> False

        b_res <- expensive new_f `underLambda` b'

        res <- go b_res

        return (b:b':res)

    go b = return [b]

