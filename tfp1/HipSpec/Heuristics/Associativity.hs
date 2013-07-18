{-# LANGUAGE ViewPatterns #-}
module HipSpec.Heuristics.Associativity where

import Test.QuickSpec.Equation
import Test.QuickSpec.Term hiding (depth)

-- If term is a function applied to two terms, Just return them
unbin :: Term -> Maybe (Symbol,Term,Term)
unbin (App (App (Const f) x) y) = Just (f,x,y)
unbin _ = Nothing

-- True if equation is an associativity equation
eqIsAssoc :: Equation -> Bool
eqIsAssoc
    ((unbin -> Just (f0,Var x0,unbin -> Just (g0,Var y0,Var z0)))
     :=:
     (unbin -> Just (f1,unbin -> Just (g1,Var x1,Var y1),Var z1)))
  = and [ f0 == f1 , g0 == g1 , f0 == g0
        , x0 == x1 , y0 == y1 , z0 == z1
        , x0 /= y0 , y0 /= z0 ]
eqIsAssoc _ = False

