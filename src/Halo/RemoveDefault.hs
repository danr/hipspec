{-

    For the contracts checker, HaloConf needs unroll_default, which does this:

    Add a BAD -> BAD and _ -> UNR alternative. If there already exists
    a DEAFAULT branch, add all the other constructors.

    The we used to add a UNR -> UNR branch if there already was a
    default branch, but this is unsound. Consider this function:

        f = \ x -> case x of
            True -> True
            _ ->ore
                False -> False
                _ -> BAD

    The last branch to BAD will never happen, but this alternative
    will translate to:

        ! [X] : ((X != True & X != False & X != UNR & X != BAD) => f(X) = BAD)

    I.e. for some untyped point *, we get f(*) = BAD, which is bad
    because now the true contract f ::: CF --> CF is satisfiable.
    Disaster!

    By unrolling all constructors, we get this:

        f = \ x -> case x of
            True -> True
            False -> case x of
                False -> False
                True -> BAD

    The last branch will now get the conflicting constraint
    X = True & X = False, not included in the file. Hooray!

    Invariant: we never get a case that looks like this

        case x of
            _ -> e

    While this creature is not often (never?) seen in GHC Core in the
    wild, we can catch these in Halo.Binds instead than here.

    For HipSpec, it's unknown if an analogous problem exists.

    We need to do this in a UniqSM monad to put some variables in the
    bound fields of alternatives.

-}
module Halo.RemoveDefault where


import CoreSyn
import CoreUtils hiding (findAlt)
import DataCon
import FastString
import TyCon
import Type
import Unique
import UniqSupply
import Id

import Control.Monad
import Control.Applicative

import Halo.Shared

removeDefaults :: [CoreBind] -> UniqSM [CoreBind]
removeDefaults = mapM rm
  where
    rm (NonRec f e) = NonRec f <$> removeDefault e
    rm (Rec fses)   = Rec <$> mapM (\(f,e) -> (,) f <$> removeDefault e) fses

removeDefault :: CoreExpr -> UniqSM CoreExpr
removeDefault e = case e of
    Var _           -> return e
    Lit _           -> return e
    App e1 e2       -> App <$> removeDefault e1 <*> removeDefault e2
    Lam x e'        -> Lam x <$> removeDefault e'
    Let _ _         -> error $ "Halo.removeDefault on let " ++ showExpr e
    Case s t w alts -> Case <$> removeDefault s <.> t <.> w
                            <*> (mapM removeDefaultInAlt <=< unrollDefault) alts
    Cast e' c       -> Cast <$> removeDefault e' <.> c
    Type _          -> return e
    Tick t e'       -> Tick t <$> removeDefault e'
    Coercion _      -> return e

removeDefaultInAlt :: CoreAlt -> UniqSM CoreAlt
removeDefaultInAlt (ac,bs,rhs) = (,,) ac bs <$> removeDefault rhs

infixl 4 <.>
(<.>) :: Applicative f => f (a -> b) -> a -> f b
f <.> x = f <*> pure x

int_err :: String -> a
int_err s = error $ "unrollDefault internal error : " ++ s

unrollDefault :: [CoreAlt] -> UniqSM [CoreAlt]
unrollDefault alts0 = case findDefault alts0 of
    (alts,Nothing)      -> return alts
    (alts,Just def_rhs) -> case alts of
        (DataAlt dc,_,_):_ -> unroll (dataConTyCon dc) alts def_rhs
        (LitAlt _  ,_,_):_ -> return alts
        _                  -> return (int_err "DEFAULT?")
  where
    unroll :: TyCon -> [CoreAlt] -> CoreExpr -> UniqSM [CoreAlt]
    unroll ty_con alts rhs = case tyConDataCons_maybe ty_con of
        Just dcs -> forM dcs (\dc -> fromMaybeM (makeAlt rhs dc)
                                                (findAlt alts dc))
        Nothing  -> return (int_err "non-data TyCon?")

findAlt :: [CoreAlt] -> DataCon -> Maybe CoreAlt
findAlt (alt@(DataAlt dc',_,_):_) dc | dc' == dc = Just alt
findAlt (_:alts) dc = findAlt alts dc
findAlt []       _  = Nothing

fromMaybeM :: Monad m => m a -> Maybe a -> m a
fromMaybeM _ (Just x) = return x
fromMaybeM m Nothing  = m

makeAlt :: CoreExpr -> DataCon -> UniqSM CoreAlt
makeAlt rhs dc = do
    bound <- mapM (\ty -> dummy_var ty <$> getUniqueM) (dataConRepArgTys dc)
    return (DataAlt dc,bound,rhs)
  where
    dummy_var :: Type -> Unique -> Var
    dummy_var ty u = mkSysLocal (fsLit "d") u ty

