{-# LANGUAGE ScopedTypeVariables, PackageImports #-}
{-

    Annoyances with the Default branch:

        * Functions that should be equal are not, such as f and g here:

            f x = case x of
                True -> e
                _    -> e'

            g x = case x of
                True  -> e
                False -> e'

        * GHC Core likes to recase on a variable that is already known, such as here:

            h x = case x of
                True -> True
                _ -> case x of
                    False -> False
                    _ -> undefined

          The call to undefined can never be reached here. Such cases should be
          removed. It also lead to a problem in the contracts checker:

          The last branch to BAD will never happen, but the alternative
          was translated to:

             ! [X] : ((X != True & X != False & X != UNR & X != BAD) => h(X) = BAD)

          I.e. for some untyped point *, we get h(*) = BAD, which is bad
          because now the true contract h ::: CF --> CF is satisfiable.
          Disaster!

          By unrolling all constructors, we get this:

              f = \ x -> case x of
                  True -> True
                  False -> case x of
                      False -> False
                      True -> BAD

          Now, x can be inlined by known-case.

    We need to do this in a m monad to put some variables in the
    bound fields of alternatives.

    TODO: We currently look at some data constructor's type constructor,
    which means we can get a problem if we have

        case e of { _ -> e' },

    we could check the type of e instead. If it is a type constructor
    with data constructors, we could unroll it.

-}
module RemoveDefault where

import CoreSyn
import CoreUtils hiding (findAlt)
import DataCon
import FastString
import TyCon
import "ghc" Type
import Unique
import UniqSupply
import Id
import DataConPattern

import Utils

import Control.Monad
import Control.Applicative

removeDefaults :: (Applicative m,MonadUnique m) => [CoreBind] -> m [CoreBind]
removeDefaults = mapM rmdBind

rmdBind :: (Applicative m,MonadUnique m) => CoreBind -> m CoreBind
rmdBind (NonRec f e) = NonRec f <$> rmdExpr e
rmdBind (Rec fses)   = Rec <$> mapM (\ (f,e) -> (,) f <$> rmdExpr e) fses

rmdExpr :: (Applicative m,MonadUnique m) => CoreExpr -> m CoreExpr
rmdExpr e0 = case e0 of
    App e1 e2       -> App <$> rmdExpr e1 <*> rmdExpr e2
    Lam x e         -> Lam x <$> rmdExpr e
    Let b e         -> Let <$> rmdBind b <*> rmdExpr e
    Case s t w alts -> Case <$> rmdExpr s <.> t <.> w
                            <*> (mapM rmdAlt <=< unrollDefault (exprType s)) alts
    Cast e c        -> Cast <$> rmdExpr e <.> c
    Tick t e        -> Tick t <$> rmdExpr e

    Type{}          -> return e0
    Var{}           -> return e0
    Lit{}           -> return e0
    Coercion{}      -> return e0

rmdAlt :: (Applicative m,MonadUnique m) => CoreAlt -> m CoreAlt
rmdAlt (ac,bs,rhs) = (,,) ac bs <$> rmdExpr rhs

infixl 4 <.>
(<.>) :: Applicative f => f (a -> b) -> a -> f b
f <.> x = f <*> pure x

unrollDefault :: forall m . (Applicative m,MonadUnique m) => Type -> [CoreAlt] -> m [CoreAlt]
unrollDefault t alts0 = case findDefault alts0 of
    (alts,Nothing)      -> return alts
    (alts,Just def_rhs) -> case alts of
        (DataAlt dc,_,_):_ -> unroll (dataConTyCon dc) alts def_rhs
        (LitAlt _  ,_,_):_ -> return alts0
        (DEFAULT   ,_,_):_ -> error "RemoveDefault.unrollDefault: duplicate DEFAULT"
        []                 -> return alts0
            -- only DEFAULT, this can be remedied by looking at the TyCon from
            -- the case scrutinee expression's type
  where
    unroll :: TyCon -> [CoreAlt] -> CoreExpr -> m [CoreAlt]
    unroll ty_con alts rhs = case tyConDataCons_maybe ty_con of
        Just dcs -> forM dcs $ \ dc ->
            fromMaybeM (makeAlt t rhs dc) (findAlt alts dc)
        Nothing  -> error "RemoveDefault.unrollDefault: non-data TyCon?"
            -- This could be remedied by just returning alts here,
            -- but it would be interesting what this ty_con really is,
            -- maybe we can do something better

findAlt :: [CoreAlt] -> DataCon -> Maybe CoreAlt
findAlt (alt@(DataAlt dc',_,_):_) dc | dc' == dc = Just alt
findAlt (_:alts) dc = findAlt alts dc
findAlt []       _  = Nothing

fromMaybeM :: (Applicative m,MonadUnique m) => Monad m => m a -> Maybe a -> m a
fromMaybeM _ (Just x) = return x
fromMaybeM m Nothing  = m

makeAlt :: (Applicative m,MonadUnique m) => Type -> CoreExpr -> DataCon -> m CoreAlt
makeAlt t rhs dc = case dcAppliedTo t dc of
    (_,Just s) -> do
        bound <- mapM (\ ty -> dummy_var (substTy s ty) <$> getUniqueM) (dataConRepArgTys dc)
        return (DataAlt dc,bound,rhs)
    _ -> error $ "RemoveDefault.makeAlt unification error:"
                 ++ "\n\t" ++ showOutputable t
                 ++ "\n\t" ++ showOutputable dc
  where
    dummy_var :: Type -> Unique -> Var
    dummy_var ty u = mkSysLocal (fsLit "d") u ty

