module Halo.Shared where

import Id
import Name
import Outputable
import PprCore
import CoreSyn
import CoreSubst

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
