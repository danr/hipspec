{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, ViewPatterns #-}
module HipSpec.Unify where

import HipSpec.Lang.Simple

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Control.Applicative

import Control.Unification
import Control.Unification.IntVar

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Error

import Data.Maybe

type UType a = UTerm (UTy a) IntVar

data UTy a r
    = UAppTy r r
    | UArrTy r r
    | UTyCon a
  deriving (Show,Functor,Foldable,Traversable)

data U a = U a | Fresh Int
  deriving (Show)

data IExpr a
    = IVar a IntVar
    | IFun (Typed a) [IntVar]
    | IApp (IExpr a) (IExpr a)

toType :: Eq a => UType a -> UnifyM a (Type (U a))
toType t0 = go =<< lift (lift (fullprune t0))
  where
    go (UVar iv@(IntVar i)) = do
        m_t <- lift (lift (lookupVar iv))
        case m_t of
            Just (UVar jv) | jv == iv -> return (TyVar (Fresh i))
            Nothing                   -> return (TyVar (Fresh i))
            Just t'                   -> go t'
    go (UTerm t) = case t of
        UArrTy u v -> ArrTy <$> go u <*> go v
        UAppTy u v   -> do
            TyCon tc ts <- go u
            t' <- go v
            return (TyCon tc (ts ++ [t']))
        UTyCon tc  -> return (TyCon (U tc) [])

type Failure a = UnificationFailure (UTy a) IntVar

type UnifyM a =
    StateT [(a,IntVar)]
        (ErrorT (Failure a)
            (IntBindingT (UTy a)
                Identity
            )
        )

uAppTys :: UType a -> [UType a] -> UType a
uAppTys = foldl (\ t x -> UTerm (UAppTy t x))

freshInst :: forall a . Eq a => Type a -> UnifyM a (UType a,[IntVar])
freshInst (collectForalls -> (tvs,t0)) = do
    m :: [(a,IntVar)] <- sequence [ (,) tv <$> lift (lift freeVar) | tv <- tvs ]

    let go t = case t of
            TyVar a     -> UVar (fromJust (lookup a m))
            ArrTy u v   -> UTerm (UArrTy (go u) (go v))
            TyCon tc ts -> uAppTys (UTerm (UTyCon tc)) (map go ts)
            Forall{}    -> fail "Forall"
            Star{}      -> fail "Star"

    return (go t0,map snd m)

instance Eq a => Unifiable (UTy a) where
    zipMatch (UArrTy u1 u2) (UArrTy v1 v2)       = Just (UArrTy (Right (u1,v1)) (Right (u2,v2)))
    zipMatch (UTyCon a)     (UTyCon b)  | a == b = Just (UTyCon a)
    zipMatch (UAppTy u1 u2) (UAppTy v1 v2)       = Just (UAppTy (Right (u1,v1)) (Right (u2,v2)))
    zipMatch _              _                    = Nothing

runGen :: Eq a => UnifyM a b -> Either (Failure a) b
runGen m0 = runIdentity $ evalIntBindingT $ runErrorT $ evalStateT m0 []

occur :: Either (Failure String) (UType String)
occur = runGen $ do
    v <- UVar <$> lift (lift freeVar)
    lift $ unifyOccurs v (UTerm (UArrTy v v))


insertVar :: Eq a => a -> UnifyM a (a,IntVar)
insertVar x = do
    t :: IntVar <- lift (lift freeVar)
    let p = (x,t)
    modify (p:)
    return p

insertVars :: Eq a => [a] -> UnifyM a [(a,IntVar)]
insertVars = mapM insertVar

lookupVars :: Eq a => [(a,IntVar)] -> UnifyM a [(a,Type (U a))]
lookupVars vs = forM vs $ \ (x,v) -> (,) x <$> varType v

genExpr :: Eq a => Expr (Typed a) -> UnifyM a (UType a,IExpr a)
genExpr e0 = case e0 of
    Var xt@(x ::: t) _ts -> do
        r <- gets (lookup x)
        case r of
            Just i  -> return (UVar i,IVar x i)
            Nothing -> do
                (rt,new) <- freshInst t
                return (rt,IFun xt new)
    App e1 e2 -> do
        (t1,i1) <- genExpr e1
        (t2,i2) <- genExpr e2
        (a,r) <- case t1 of
            UTerm (UArrTy a r) -> return (a,r)
            UVar{} -> do
                a <- UVar <$> lift (lift freeVar)
                r <- UVar <$> lift (lift freeVar)
                void $ lift $ unifyOccurs t1 (UTerm (UArrTy a r))
                return (a,r)
            _ -> fail "genExpr: ill-typed expression"
        void $ lift $ unifyOccurs t2 a
        return (r,IApp i1 i2)
    Lit _ (_tc ::: _) -> error "Unify for literals not implemented!"
                      -- return (UTerm (UTyCon tc))

varType :: Eq a => IntVar -> UnifyM a (Type (U a))
varType iv = do
    m_t <- lift (lift (lookupVar iv))
    case m_t of
        Just t  -> toType t
        Nothing -> toType (UVar iv) -- (TyVar (Fresh i))
--    return (toType t)

extExpr :: Eq a => IExpr a -> UnifyM a (Expr (Typed (U a)))
extExpr i0 = case i0 of
    IVar x i -> do
        t <- varType i
        return $ Var (U x ::: t) []
    IFun xt is -> do
        ts <- mapM varType is
        return $ Var (fmap U xt) (map star ts)
    IApp i1 i2 -> App <$> extExpr i1 <*> extExpr i2


{-

runExpr sc e = runGen $ do
    insertVars sc
    (t,i) <- genExpr e
    e' <- extExpr i
    t' <- toType t
    sc' <- readVars
    return (t',e',sc')

infixr -->
(-->)  = ArrTy

infixl @@
(@@) = App

test_occur :: Expr (Typed String)
test_occur =
    Var ("x" ::: undefined) [] @@
    Var ("x" ::: undefined) []

test :: Expr (Typed String)
test =
    Var ("length" ::: (Forall "a" (list a --> nat))) [undefined] @@
    Var ("x" ::: list nat) []
  where
    a      = TyVar "a"
    list b = TyCon "List" [b]
    nat    = TyCon "Nat" []

test' :: Expr (Typed String)
test' =
    Var ("id" ::: (Forall "a" (a --> a))) [undefined] @@
    Var ("x" ::: nat) []
  where
    a      = TyVar "a"
    list b = TyCon "List" [b]
    nat    = TyCon "Nat" []

test_const :: Expr (Typed String)
test_const =
    Var ("const" ::: (Forall "a" (Forall "b" (a --> b --> a)))) [undefined,undefined] @@
    Var ("x" ::: undefined) [] @@
    Var ("y" ::: undefined) []
  where
    a = TyVar "a"
    b = TyVar "b"

test_map_join :: Expr (Typed String)
test_map_join = map @@ join @@ Var ("x" ::: undefined) []
  where
    a = TyVar "a"
    b = TyVar "b"
    list b = TyCon "List" [b]
    map = Var ("map" ::: Forall "a" (Forall "b" ((a --> b) --> list a --> list b))) [undefined,undefined]
    join = Var ("join" ::: Forall "a" (list (list a) --> list a)) [undefined]

-}
