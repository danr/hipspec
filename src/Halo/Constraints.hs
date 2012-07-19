{-# LANGUAGE ViewPatterns #-}
module Halo.Constraints where

import CoreSubst
import CoreSyn
import DataCon
import Outputable
import Var
import Name hiding (varName)

import Halo.Shared

import Data.List

-- Constraints from case expressions to results, under a substitution
data Constraint
    = Equality   CoreExpr DataCon [CoreExpr]
    | Inequality CoreExpr DataCon

instance Show Constraint where
    show constr = case constr of
        Equality e dc bs ->
            showExpr e ++ " = " ++ showOutputable dc
              ++ "(" ++ intercalate "," (map showOutputable bs) ++ ")"
        Inequality e dc ->
             showExpr e ++ " != " ++ showOutputable dc

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
conflict cs = or
    $ -- Conflict if C1(...) /= C1(...)
        [ cheapExprEq e1 e2 && con_x == con_y
        | Equality   e1 con_x _ <- cs
        , Inequality e2 con_y <- cs
        ]
        -- Conflict if C1(...) = C2(...)
     ++ [ cheapExprEq e1 e2 && con_x /= con_y
        | Equality e1 con_x _ <- cs
        , Equality e2 con_y _ <- cs
        ]
        -- Conflict if Inequality C1 C2(..), but C1 == C2
     ++ [ dataConName con == varName x
        | Inequality (collectArgs -> (Var x,_)) con <- cs
        ]

cheapExprEq :: CoreExpr -> CoreExpr -> Bool
cheapExprEq (Var x) (Var y) = x == y
cheapExprEq (App e1 e2) (App e1' e2') = cheapExprEq e1 e2 &&
                                        cheapExprEq e1' e2'
cheapExprEq _ _ = False

rmRedundantConstraints :: [Constraint] -> [Constraint]
rmRedundantConstraints = nubBy laxConstrEq . filter (not . redundant)

laxConstrEq :: Constraint -> Constraint -> Bool
laxConstrEq (Equality e1 con1 as1) (Equality e2 con2 as2)
    = cheapExprEq e1 e2 && con1 == con2 && and (zipWith cheapExprEq as1 as2)
laxConstrEq (Inequality e1 con1) (Inequality e2 con2)
    = cheapExprEq e1 e2 && con1 == con2
laxConstrEq _ _ = False

redundant :: Constraint -> Bool
redundant c = case c of
    -- C1 /= C2 is redundant information, if C1 really is a constructor
    Inequality (collectArgs -> (Var x,_xs)) con
        -> dataConName con /= varName x
            && not (isVarName (varName x)) && isDataConName (varName x)
            -- ^ this check is needed or OccName.isDataCon blows up
    -- C1 == C1 is redundant information,
    -- but what to do if it has arguments?
    Equality (collectArgs -> (Var x,[])) con []
        -> dataConName con == varName x
    _ -> False
