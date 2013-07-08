{-# LANGUAGE PatternGuards #-}
-- | Simplify pass over the rich language:
--
--  * Inlines local non-recursive definitions,
--  * Eliminates known-case:
--      - when the scrutinee expression is a constructor
--      - by inlining/eliminating the scrutinee variable
--  * Beta reduction
--
-- These passes destroy sharing and make the program less efficient.
-- However, they should preserve the semantics (even in presence of
-- non-terminating programs/bottoms)
--
-- TODO: Inline non-recursive global definitions
--       Polymorphic lets
module SimplifyRich where

import Rich
import Type

simpFun :: Eq a => Function (Typed a) -> Function (Typed a)
simpFun (Function f b) = Function f $ simpExpr $ case b of
    -- Sometimes functions look like this
    -- f = let g = K[g] in g,
    -- then we simply replace it to f = K[f]
    -- TODO: Polymorphic functions (find examples!)
    Let [Function g e] (Var g' [])
        | not (isForallTy (typed_type g)), g == g' -> (Var f [] // g) e
    _ -> b

simpExpr :: Eq a => Expr (Typed a) -> Expr (Typed a)
simpExpr = transformExpr $ \ e0 -> case e0 of

    -- Beta reduction
    App (Lam x body) arg -> simpExpr ((arg // x) body)

    -- Known case on a constructor
    Case e x alts
        | (Var u ts,args) <- collectArgs e
        , Just (ConPat _ _ bs,rhs)  <- findAlt u ts alts
        -> simpExpr (substMany ((x,e):zip bs args) rhs)

    Case e x alts -> Case e x [ (p,simpExpr (removeScrutinee e x alt))
                              | alt@(p,_) <- alts
                              ]

    -- Inlining local non-recursive functions
    -- TODO: Handle several functions, handle polymorphic functions (no examples yet)
    Let [Function f b] e
        | not (isForallTy (typed_type f))
        , not (f `occursIn` b) -> simpExpr ((b // f) e)

    _ -> e0

-- | Removes the scrutinee variable (and also the expression if it is a variable),
--   by inlining the pattern or the expression again (if it is a Default alt)
removeScrutinee :: Eq a => Expr (Typed a) -> Typed a -> Alt (Typed a) -> Expr (Typed a)
removeScrutinee e x (p,rhs) = subst rhs
  where
    subst_expr  = case p of
        Default  -> e
        LitPat l -> Lit l (error "lit pat type! :(")
        ConPat u ts bs -> apply (Var u ts) (map (`Var` []) bs)

    -- If the scrutinee is just a variable, we inline it too.
    -- This can lead to triggering many known case.
    subst = substMany . (`zip` repeat subst_expr) . (x:) $ case e of
        Var u [] -> [u]   -- The variable can only be locally bound by lambda
                          -- or case and thus is not applied to type args.
        _        -> []

