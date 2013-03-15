{-# LANGUAGE PatternGuards, CPP, ViewPatterns #-}
{-

    Shared functions operating on GHC

-}
module Halo.Shared where

import CoreFVs
import CoreSubst
import CoreSyn
import DataCon
import Id
import MkCore (errorIds)
import Name hiding (varName)
import Outputable
import PprCore
import PrelNames
import TyCon
import Type (Type, repType,
    splitTyConApp_maybe, splitAppTy_maybe, splitFunTy_maybe)
#if __GLASGOW_HASKELL__ >= 706
import Type (flattenRepType)
import DynFlags (tracingDynFlags)
#endif
import UniqSet
import Var

import qualified Data.Map as M
import Data.Maybe

import Data.List

-- | Drop in replacement for repType
repType' :: Type -> Type
#if __GLASGOW_HASKELL__ >= 706
repType' = fromMaybe (error "repType'") . listToMaybe . flattenRepType . repType
#else
repType' = repType
#endif

-- | showSDoc that works with both ghc 7.4.1 and 7.6.1.
--   TODO: 7.4.2 introduced this change, how to get that granularity?
portableShowSDoc :: SDoc -> String
#if __GLASGOW_HASKELL__ >= 706
portableShowSDoc = showSDoc tracingDynFlags
#else
portableShowSDoc = showSDoc
#endif

-- | Makes Rec or NonRec depending on input list length is 1 or not
mkCoreBind :: [(Var,CoreExpr)] -> CoreBind
mkCoreBind [(f,e)] = NonRec f e
mkCoreBind fses    = Rec fses

-- | Shows something outputable
showOutputable :: Outputable a => a -> String
showOutputable = portableShowSDoc . ppr

-- | Short representation of an Id/Var to String
idToStr :: Id -> String
idToStr = showOutputable . maybeLocaliseName . idName
  where
    maybeLocaliseName n
        | isSystemName n = n
        | otherwise      = localiseName n

-- | Shows a Core Expression
showExpr :: CoreExpr -> String
showExpr = portableShowSDoc . pprCoreExpr

-- | If a binder alternates between binding type variables and normal
--   variables, this one strips off all the type variables.
collectBindersDeep :: CoreExpr -> ([Var],CoreExpr)
collectBindersDeep = go
  where
    go e = case collectTyAndValBinders e of
       (_ty,args,e')
           | Lam _ _ <- e' -> let (r_args,r_e) = go e'
                              in  (args ++ r_args,r_e)
           | otherwise     -> (args,e')

-- | The arity of an expression if it is a lambda
exprArity :: CoreExpr -> Int
exprArity = length . fst . collectBindersDeep

-- | Removes the type arguments
trimTyArgs :: [CoreArg] -> [CoreArg]
trimTyArgs = filter (not . isTyArg)
  where
    isTyArg Type{}     = True
    isTyArg Coercion{} = True
    isTyArg _          = False

-- | @subst e x y@ substitutes as e[y/x] but does not touch global ids
subst :: Var -> Var -> CoreExpr -> CoreExpr
subst x y = substExpr (text "halo") s
  where
    s = extendIdSubst emptySubst x (Var y)

mkTyAndIdSubst :: [(Var,CoreExpr)] -> Subst
mkTyAndIdSubst = foldr (uncurry extend) emptySubst
  where
    extend x e su = case e of
        Type ty | isTyVar x -> extendTvSubst su x ty
        _                   -> extendIdSubst su x e

-- | Substitute an expression
substExp :: Var        -- ^ x
         -> CoreExpr   -- ^ ex
         -> CoreExpr   -- ^ e
         -> CoreExpr   -- ^ e[ex/x]
substExp x ex = substExpr (text "halo") (mkTyAndIdSubst [(x,ex)])

-- | Substitute a list
substList :: [(Var,Var)] -> CoreExpr -> CoreExpr
substList xs = substExpr (text "halo") (mkTyAndIdSubst xs')
  where
    xs' = [ (x,Var y) | (x,y) <- xs ]

-- | Substitute an expression list
substExprList :: [(Var,CoreExpr)] -> CoreExpr -> CoreExpr
substExprList xs = substExpr (text "halo") (mkTyAndIdSubst xs)

-- | Sometimes, we want to change potentially global ids in
--   expressions, then this function is the one
substGblId :: Id -> Id -> CoreExpr -> CoreExpr
substGblId xold xnew = go
  where
    go e0 = case e0 of
        App e1 e2         -> App (go e1) (go e2)
        Lam x e           -> Lam x (go e)
        Let _ _           -> error $ "Halo.Shared.substGblId on let: " ++ showExpr e0
        Case s t w alts   -> Case (go s) t w (map go_alt alts)
        Cast e c          -> Cast (go e) c
        Tick t e          -> Tick t (go e)
        Var x | x == xold -> Var xnew
        Var{}             -> e0
        Lit{}             -> e0
        Type{}            -> e0
        Coercion{}        -> e0

    go_alt (pat,bs,rhs) = (pat,bs,go rhs)

-- | Substitute many (potentially) global ids
substGblIds :: [(Id,Id)] -> CoreExpr -> CoreExpr
substGblIds = flip (foldr (uncurry substGblId))

-- | Simple application to get rid of some lambdas
(@@) :: CoreExpr -> CoreExpr -> CoreExpr
Lam x e1 @@ e2 = substExp x e2 e1
e1       @@ e2 = App e1 e2

-- | Apply many expressions to an expression
foldApps :: CoreExpr -> [CoreExpr] -> CoreExpr
foldApps = foldl App

-- | Attempts to find the rhs of a variable in a binding list.
--   Can be bound partially applied to get a thunk specialised for a
--   set of binds.
lookupBind :: [CoreBind] -> Var -> CoreExpr
lookupBind bs =
    let bs_map = M.fromList (flattenBinds bs)
    in \v ->
        let err = error $ "lookup_bind: lost binding for " ++ showOutputable v
        in fromMaybe err (M.lookup v bs_map)

-- | Is this Id a "constructor" to a newtype?
--   This is the only way I have found to do it...
isNewtypeConId :: Id -> Bool
isNewtypeConId i
    | Just dc <- isDataConId_maybe i = isNewTyCon (dataConTyCon dc)
    | otherwise = False

-- | Is this Id a data or newtype constructor?
--
--   Note: cannot run isDataConWorkId on things that aren't isId,
--         then we get a panic from idDetails.
isDataConId :: Id -> Bool
isDataConId v = isId v && (isConLikeId v || isNewtypeConId v)

-- | Free non-type variables in an expression, local or global
--
--   For now, an ugly hack to not get stuck in GHC.Base.patError,
--   or in String literals
exprFVs :: CoreExpr -> [Var]
exprFVs = uniqSetToList . exprSomeFreeVars (\v ->
    (isLocalId v || isGlobalId v) && not (isDataConId v)
        && v `notElem` errorIds
        && nameModule_maybe (varName v) /= Just gHC_CSTRING)

-- | Removes Cast and Tick
removeCruft :: CoreExpr -> CoreExpr
removeCruft e = case e of
    Var x     -> Var x
    Lit i     -> Lit i
    App e1 e2 -> App (removeCruft e1) (removeCruft e2)
    Lam x e'  -> Lam x (removeCruft e')
    Let _ _   -> error $ "Halo.Shared.removeCruft on let " ++ showExpr e
    Case s t w alts -> Case (removeCruft s) t w (map rmAltCruft alts)
    Cast e' _rm     -> e'
    Type t          -> Type t
    Tick _rm e'     -> e'
    Coercion co     -> Coercion co
  where
    rmAltCruft (pat,bs,rhs) = (pat,bs,removeCruft rhs)

-- | Id and Arity of a DataCon
dcIdArity :: DataCon -> (Id,Int)
dcIdArity dc = (dataConWorkId dc,dataConRepArity dc)

dcIdArgTypes :: DataCon -> (Id,[Type])
dcIdArgTypes dc = (dataConWorkId dc,dataConRepArgTys dc)

cheapExprEq :: CoreExpr -> CoreExpr -> Bool
cheapExprEq (Var x)     (Var y)       = x == y
cheapExprEq (Lam x e1)  (Lam y e2)    = x == y && cheapExprEq e1 e2
cheapExprEq (App e1 e2) (App e1' e2')
    = cheapExprEq e1 e2 && cheapExprEq e1' e2'
cheapExprEq _ _ = False


typeTyCons :: Type -> [TyCon]
typeTyCons = nub . go where
    -- repType' looks through foralls,
    -- synonyms, predicates and newtypes
    go (repType' -> t)
        | Just (t1,t2) <- splitFunTy_maybe t = go t1 ++ go t2
        | Just (ty_con,ts) <- splitTyConApp_maybe t = ty_con:concatMap go ts
        | Just (t1,t2) <- splitAppTy_maybe t = go t1 ++ go t2
        | otherwise = []

varTypeTyCons :: Var -> [TyCon]
varTypeTyCons = typeTyCons . varType

