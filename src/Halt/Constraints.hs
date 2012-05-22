module Halt.Constraints where

import CoreSubst
import CoreSyn
import DataCon
import Outputable

import Halt.Utils

-- Constraints from case expressions to results, under a substitution
data Constraint = Equality   CoreExpr DataCon [CoreExpr]
                | Inequality CoreExpr DataCon

instance Show Constraint where
  show (Equality   e _dc _bs) = showExpr e ++ " == fix constraint show instance" -- ++ show p
  show (Inequality e _dc)     = showExpr e ++ " /= fix constraint show instance" -- ++ show p

-- | Substitute in the constraints
substConstr :: Subst -> Constraint -> Constraint
substConstr s c = case c of
    Equality e dc bs -> Equality (substExpr (text "substConstr") s e) dc
                                 (map (substExpr (text "substConstr") s) bs)
    Inequality e dc  -> Inequality (substExpr (text "substConstr") s e) dc

-- | The empty constraints
noConstraints :: [Constraint]
noConstraints = []


conflict :: [Constraint] -> Bool
conflict cs = or [ cheapExprEq e1 e2 && con_x == con_y
                 | Equality   e1 con_x _ <- cs
                 , Inequality e2 con_y <- cs
                 ]
  where
    cheapExprEq :: CoreExpr -> CoreExpr -> Bool
    cheapExprEq (Var x) (Var y) = x == y
    cheapExprEq (App e1 e2) (App e1' e2') = cheapExprEq e1 e2 &&
                                            cheapExprEq e1' e2'
    cheapExprEq _ _ = False

