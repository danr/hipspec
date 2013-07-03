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

    Case e x alts -> Case e x [ (p,simpExpr (removeScrutinee e x rhs))
                              | (p,rhs) <- alts
                              ]

    -- Inlining local non-recursive functions
    -- TODO: Handle several functions, handle polymorphic functions (no examples yet)
    Let [Function f [] _ b] e | not (f `occursIn` b) -> simpExpr ((b // f) e)

    _ -> e0

-- | Removes the scrutinee variable (and also the expression if it is a variable),
--   by inlining the pattern or the expression again (if it is a Default alt)
removeScrutinee :: Expr a -> a -> Alt a -> Expr a
removeScrutinee e x (p,rhs) = subst rhs
  where
    subst_expr  = case p of
        Default        -> e
        ConPat u ts bs -> apply (Var u ts) (map (`Var` []) bs)
        LitPat l       -> Lit l

    -- If the scrutinee is just a variable, we inline it too.
    -- This can lead to triggering many known case.
    subst = substMany . (`zip` repeat subst_expr) . (x:) $ case e of
        Var u [] -> [u]   -- TODO: type variables applied to this variable?
        _        -> []

