module Hip.Trans.Property where

import Hip.Trans.Theory
import Hip.Trans.SrcRep

import CoreSyn
import Var
import TysWiredIn
import CoreFVs
import UniqSet

import Halo.Shared

import Control.Arrow (second)

trProperty :: CoreBind -> Maybe Prop
trProperty (NonRec prop_name e) = do
    let (ty_vars,vars,e0) = collectTyAndValBinders e

        (oops,e_prop) = case second trimTyArgs (collectArgs e0) of
                            (Var x,[prop]) | isOops x -> (True,prop)
                            _                         -> (False,e0)

    (lhs,rhs) <- case second trimTyArgs (collectArgs e_prop) of
                       (Var x,[l,r]) | isEquals x    -> Just (l,r)
                       (Var x,[l])   | isProveBool x -> Just (l,Var trueDataConId)
                       _  -> Nothing

    -- Free variables, but do not count =:=, proveBool, oops or arguments
    let free = (exprFreeVars lhs `unionUniqSets` exprFreeVars rhs)
                  `delListFromUniqSet` (vars ++ ty_vars)

    return $ Prop { propName    = idToStr prop_name
                  , proplhs     = lhs
                  , proprhs     = rhs
                  , propVars    = [ (x,varType x) | x <- vars ]
                  , propRepr    = showExpr lhs ++ " = " ++ showExpr rhs
                  , propQSTerms = error "trProperty : propQSTerms"
                  , propFunDeps = uniqSetToList free
                  , propOops    = oops
                  }
trProperty _ = Nothing
