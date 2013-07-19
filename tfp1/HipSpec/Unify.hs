{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, ViewPatterns, ScopedTypeVariables #-}
module HipSpec.Unify {- (toType,UType,runGen,withScope,genExpr,U(..)) -} where

import Control.Unification
import Control.Unification.IntVar
import Control.Monad.Identity

import Data.Traversable (Traversable)
import Data.Foldable (Foldable)

import HipSpec.Lang.Type
import HipSpec.Lang.Simple
import Control.Applicative

import Data.Maybe

import Control.Monad.State
import Control.Monad.Error

type UType a = UTerm (UTy a) IntVar

data UTy a r
    = UApp r r
    | UArrTy r r
    | UTyCon a
  deriving (Show,Functor,Foldable,Traversable)

data U a = U a | Fresh Int
  deriving (Show)

toType :: UType a -> Type (U a)
toType (UVar (IntVar x)) = TyVar (Fresh x)
toType (UTerm t) = case t of
    UArrTy u v -> ArrTy (toType u) (toType v)
    UApp u v   ->
        let TyCon tc ts = toType u
        in  TyCon tc (ts ++ [toType v])
    UTyCon tc  -> TyCon (U tc) []

type Failure a = UnificationFailure (UTy a) IntVar

type UnifyM a =
    StateT [(a,IntVar)]
        (ErrorT (Failure a)
            (IntBindingT (UTy a)
                Identity
            )
        )

uapp :: UType a -> [UType a] -> UType a
uapp t []     = t
uapp t (x:xs) = uapp (UTerm (UApp t x)) xs

freshInst :: forall a . Eq a => Type a -> UnifyM a (UType a,[IntVar])
freshInst (collectForalls -> (tvs,t0)) = do
    m :: [(a,IntVar)] <- sequence [ (,) tv <$> lift (lift freeVar) | tv <- tvs ]

    let go t = case t of
            TyVar a     -> UVar (fromJust (lookup a m))
            ArrTy u v   -> UTerm (UArrTy (go u) (go v))
            TyCon tc ts -> uapp (UTerm (UTyCon tc)) (map go ts)
            Forall{}    -> fail "Forall"
            Star{}      -> fail "Star"

    return (go t0,map snd m)

instance Eq a => Unifiable (UTy a) where
    zipMatch (UArrTy u1 u2) (UArrTy v1 v2)          = Just (UArrTy (Right (u1,v1)) (Right (u2,v2)))
    zipMatch (UTyCon a)     (UTyCon b)  | a == b    = Just (UTyCon a)
    zipMatch (UApp u1 u2)   (UApp v1 v2)            = Just (UApp (Right (u1,v1)) (Right (u2,v2)))
    zipMatch _              _                       = Nothing

runGen :: Eq a => UnifyM a b -> Either (Failure a) b
runGen m0 = runIdentity $ evalIntBindingT $ runErrorT $ evalStateT m0 []

insertVar :: Eq a => a -> UnifyM a ()
insertVar x = do
    t :: IntVar <- lift (lift freeVar)
    modify ((x,t):)

insertVars :: Eq a => [a] -> UnifyM a ()
insertVars = mapM_ insertVar

readVars :: forall a . (Show a,Eq a) => UnifyM a [(a,Type (U a))]
readVars = do
    vs :: [(a,IntVar)] <- get
    lookupVars vs

lookupVars :: (Show a,Eq a) => [(a,IntVar)] -> UnifyM a [(a,Type (U a))]
lookupVars vs = lift $ lift $ forM vs $ \ (x,v) -> do
    m_t <- lookupVar v
    case m_t of
        Just t  -> return (x,toType t)
        Nothing -> return (x,toType (UVar v))

lookupA :: Eq a => a -> UnifyM a IntVar
lookupA x = gets (fromJust . lookup x)

genExpr :: Eq a => Expr (Typed a) -> UnifyM a (UType a)
genExpr e0 = case e0 of
    Var (x ::: t) ts -> do
        r <- gets (lookup x)
        case r of
            Just i  -> return (UVar i)
            Nothing -> do
                (rt,new) <- freshInst t
                sequence_
                    [ lookupA tv >>= \ m -> lift (unify (UVar m) (UVar n))
                    | (t',n) <- ts `zip` new, let TyVar (tv ::: _) = t'
                    ]
                return rt
    App e1 e2 -> do
        t1 <- genExpr e1
        t2 <- genExpr e2
        case t1 of
            UTerm (UArrTy u v) -> do
                void $ lift $ unify u t2
                return v
            _ -> fail "genExpr: ill-typed expression"
    Lit _ (tc ::: _) -> return (UTerm (UTyCon tc))

type TempM = State Int

runTempM :: TempM a -> (a,Int)
runTempM m = runState m 0

data Temp a = Temp a | BindMe Int
  deriving (Show,Eq,Ord)

tempExpr :: Expr (Typed a) -> TempM (Expr (Typed (Temp a)))
tempExpr (Var f ts)  = Var (Temp <$> f) <$> mapM (const tempTyVar) ts
tempExpr (App e1 e2) = App <$> tempExpr e1 <*> tempExpr e2
tempExpr (Lit i tc)  = return $ Lit i (fmap Temp tc)

unTempExpr :: forall a . Eq a => [(Temp a,Type (U a))] -> Expr (Typed (Temp a)) -> Expr (Typed (U a))
unTempExpr m = go
  where
    go :: Expr (Typed (Temp a)) -> Expr (Typed (U a))
    go e0 = case e0 of
        Var (Temp f ::: t) ts -> Var (U f ::: lkty t) [ star (lktv a) | TyVar (a ::: _) <- ts ]
        App e1 e2             -> App (go e1) (go e2)
        Lit i (Temp tc ::: t) -> Lit i (U tc ::: lkty t)
        _ -> error "temporary error"

    lktv :: Temp a -> Type (U a)
    lktv a = fromJust (lookup a m)

    lkty :: Type (Temp a) -> Type (U a)
    lkty = fmap (\ (Temp a) -> U a)


tempTyVar :: TempM (Type (Typed (Temp a)))
tempTyVar = star . TyVar <$> temp

temp :: TempM (Temp a)
temp = state $ \ x -> (BindMe x,x+1)

test :: Expr (Typed String)
test = Var ("length" ::: (Forall "a" (list a --> a))) [undefined] `App` Var ("x" ::: nat) []
  where
    a      = TyVar "a"
    list b = TyCon "List" [b]
    nat    = TyCon "Nat" []
    (-->)  = ArrTy

run_test = case m_binds of
    Right binds ->
        let boo :: U (Temp a) -> U a
            boo (U (Temp a)) = U a
            boo (Fresh i)    = Fresh i
            binds' = [ (t,fmap boo ty) | (t,ty) <- binds ]
        in  (unTempExpr binds' test',lookup (Temp "x") binds')
    Left err -> error (show err)
  where
    (test',n) = runTempM (tempExpr test)
    m_binds = runGen $ do
        insertVars $ [Temp "x"] ++ map BindMe [0..n-1]
        genExpr test'
        readVars

