{-# LANGUAGE PatternGuards #-}
{-

    Shared functions operating on GHC

-}
module Halo.Shared where

import CoreFVs
import DataCon
import UniqSet
import Var
import Id
import Name
import Outputable
import PprCore
import CoreSyn
import CoreSubst

import qualified Data.Map as M
import Data.Maybe

-- | Makes Rec or NonRec depending on input list length is 1 or not
mkCoreBind :: [(Var,CoreExpr)] -> CoreBind
mkCoreBind [(f,e)] = NonRec f e
mkCoreBind fses    = Rec fses

-- | Shows something outputable
showOutputable :: Outputable a => a -> String
showOutputable = showSDoc . ppr

-- | Short representation of an Id/Var to String (unsafely for now)
idToStr :: Id -> String
idToStr = showSDocOneLine . ppr . maybeLocaliseName . idName
  where
    maybeLocaliseName n | isSystemName n = n
                        | otherwise      = localiseName n

-- | Shows a Core Expression
showExpr :: CoreExpr -> String
showExpr = showSDoc . pprCoreExpr

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

-- | @subst e x y@ substitutes as e[y/x]
subst :: CoreExpr -> Var -> Var -> CoreExpr
subst e x y = substExpr (text "halo") s e
  where
    s = extendIdSubst emptySubst x (Var y)

mkTyAndIdSubst :: [(Var,CoreExpr)] -> Subst
mkTyAndIdSubst = foldr (uncurry extend) emptySubst
  where
    extend x e su = case e of
        Type ty | isTyVar x -> extendTvSubst su x ty
        _                   -> extendIdSubst su x e

-- | Substitute an expression
substExp :: CoreExpr -> Var -> CoreExpr -> CoreExpr
substExp e x e' = substExpr (text "halo") (mkTyAndIdSubst [(x,e')]) e

-- | Substitute a list
substList :: CoreExpr -> [(Var,Var)] -> CoreExpr
substList e xs = substExpr (text "halo") (mkTyAndIdSubst xs') e
  where
    xs' = [ (x,Var y) | (x,y) <- xs ]

-- | Substitute an expression list
substExprList :: CoreExpr -> [(Var,CoreExpr)] -> CoreExpr
substExprList e xs = substExpr (text "halo") (mkTyAndIdSubst xs) e

-- | Simple application to get rid of some lambdas
(@@) :: CoreExpr -> CoreExpr -> CoreExpr
Lam x e @@ e2 = substExp e x e2
e1      @@ e2 = App e1 e2

-- | Apply many expressions to an expression
foldApps :: CoreExpr -> [CoreExpr] -> CoreExpr
foldApps = foldl App

-- | Attempts to find the rhs of a variable in a binding list
--   You can let bind this to get a thunk specialised for a set of binds
lookupBind :: [CoreBind] -> Var -> CoreExpr
lookupBind bs =
    let bs_map = M.fromList (flattenBinds bs)
    in \v ->
        let err = error $ "lookup_bind: lost binding for " ++ show v
        in fromMaybe err (M.lookup v bs_map)

-- | Free variables in an expression
exprFVs :: CoreExpr -> [Var]
exprFVs = uniqSetToList . exprFreeIds

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

-- Id and Arity of a DataCon
dcIdArity :: DataCon -> (Id,Int)
dcIdArity dc = (dataConWorkId dc,dataConRepArity dc)

cheapExprEq :: CoreExpr -> CoreExpr -> Bool
cheapExprEq (Var x) (Var y) = x == y
cheapExprEq (Lam x e1) (Lam y e2) = x == y && cheapExprEq e1 e2
cheapExprEq (App e1 e2) (App e1' e2') = cheapExprEq e1 e2 &&
                                        cheapExprEq e1' e2'
cheapExprEq _ _ = False
