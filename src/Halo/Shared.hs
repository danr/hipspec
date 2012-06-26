module Halo.Shared where

import Id
import Name
import Outputable
import PprCore
import CoreSyn

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
    isTyArg Type{} = True
    isTyArg _      = False

