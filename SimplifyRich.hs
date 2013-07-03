{-# LANGUAGE PatternGuards #-}
-- | Simplify pass over the rich language:
--
--  * Inlines local non-recursive definitions,
--  * Eliminates known-case:
--      - when the scrutinee expression is a constructor
--      - by inlining/eliminating the scrutinee variable
--  * Beta reduction
--
--  These passes destroy sharing and make the program less efficient.
--  However, they should preserve the semantics (even in presence of
--  non-terminating programs/bottoms)
module SimplifyRich where

import Rich

simpFun :: Eq a => Function a -> Function a
simpFun (Function f tvs t b) = Function f tvs t b'
  where
    b' = simpExpr $ case b of
        -- Sometimes functions look like this
        -- f = let g = K[g] in g,
        -- then we simply replace it to f = K[f]
        Let [Function g [] _ e] (Var g' []) | g == g' -> (Var f [] // g) e
        _ -> b


simpExpr :: Eq a => Expr a -> Expr a
simpExpr = transformExpr $ \ e0 -> case e0 of

    -- Beta reduction
    App (Lam x _ body _) arg -> simpExpr ((arg // x) body)

    -- Known case on a constructor
    Case e x alts
        | (Var u ts,args) <- collectArgs e
        , Just (ConPat _ _ bs,rhs)  <- findAlt u ts alts
        -> simpExpr (substMany ((x,e):zip bs args) rhs)

    -- Inlining the scrutinee variable
    -- For the default branch , we simply replace it with the expression again,
    -- otherwise it is substituted for the pattern
    Case e x alts -> Case e x $ flip map alts $ \ (p,rhs) -> (,) p . simpExpr $ case p of
        Default        -> (e // x) rhs
        ConPat u ts bs -> (apply (Var u ts) (map (`Var` []) bs) // x) rhs
        LitPat l       -> (Lit l // x) rhs

    -- Inlining local non-recursive functions
    -- TODO: Handle several functions, handle polymorphic functions (no examples yet)
    Let [Function f [] _ b] e | not (f `occursIn` b) -> simpExpr ((b // f) e)

    _ -> e0

