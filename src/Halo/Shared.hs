{-

    Shared functions operating on GHC stuff

-}
module Halo.Shared where

import CoreFVs
import UniqSet
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

-- | The arity of an expression if it is a lambda
exprArity :: CoreExpr -> Int
exprArity e = length as
  where (_,as,_) = collectTyAndValBinders e

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

-- | Substitute an expression
substExp :: CoreExpr -> Var -> CoreExpr -> CoreExpr
substExp e x e' = substExpr (text "halo") s e
  where
    s = extendIdSubst emptySubst x e'

-- | Substitute a list
substList :: CoreExpr -> [(Var,Var)] -> CoreExpr
substList e xs = substExpr (text "halo") s e
  where
    s = extendIdSubstList emptySubst [ (x,Var y) | (x,y) <- xs ]

-- | Substitute an expression list
substExprList :: CoreExpr -> [(Var,CoreExpr)] -> CoreExpr
substExprList e xs = substExpr (text "halo") s e
  where
    s = extendIdSubstList emptySubst xs

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
    Case s t w alts -> Case (removeCruft s) t w (map rmAltCruft alts)
    Cast e' _rm     -> e'
    Type t          -> Type t
    Tick _rm e'     -> e'
    Coercion co     -> Coercion co
  where
    rmAltCruft (pat,bs,rhs) = (pat,bs,removeCruft rhs)
