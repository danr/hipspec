module Hip.Trans.Property where

import Hip.Trans.Theory
import Hip.Trans.SrcRep

import CoreSyn
import Var
import TysWiredIn

import Halt.Utils

import Control.Arrow (second)

trProperty :: CoreBind -> Maybe Prop
trProperty (NonRec prop_name e) = do
    let (_,vars,e') = collectTyAndValBinders e

    (lhs,rhs) <- case second trimTyArgs (collectArgs e') of
                       (Var x,[l,r]) | isEquals x    -> Just (l,r)
                       (Var x,[l])   | isProveBool x -> Just (l,Var trueDataConId)
                       _  -> Nothing

    return $ Prop { propName = idToStr prop_name
                  , proplhs  = lhs
                  , proprhs  = rhs
                  , propVars = [ (x,varType x) | x <- vars ]
                  , propRepr = showExpr lhs ++ " = " ++ showExpr rhs
                  , propQSTerms = error "trProperty : propQSTerms"
                  }
trProperty _ = Nothing
