{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on how to
--   pretty-print variables.
module PrettyRich where

import Text.PrettyPrint.HughesPJ

import Rich

ppProg :: (a -> Doc) -> Program a -> Doc
ppProg p (Program _ds fs) = vcat (map (ppFun p) fs)

ppFun :: (a -> Doc) -> Function a -> Doc
ppFun p (Function nm tvs ty e) =
    p nm <+> "::" <+>
        (if null tvs then empty else "forall" <+> sep (map p tvs) <+> ".")
        <+> ppType 0 p ty $$
    p nm <+> "=" <+> ppExpr 0 p e

ppExpr :: Int -> (a -> Doc) -> Expr a -> Doc
ppExpr i p e0 = case e0 of
    Var x ts      -> iff (not (null ts)) parens $
                     p x <> cat [ " @" <+> ppType 1 p t | t <- ts ]
    App e1 e2     -> iff (i > 0) parens $ ppExpr 0 p e1 <+> ppExpr 1 p e2
    Lit x         -> integer x
    String        -> "\"\""
    Lam x e       -> "\\" <+> p x <+> "->" <+> ppExpr 0 p e
    Case e x alts -> "case" <+> ppExpr 0 p e <+> "of" <+> p x $$ nest 4
        (braces (vcat (punctuate ";" (map (ppAlt p) alts))))
    Let fns e ->
        ("let" $$ nest 4 (vcat (map (ppFun p) fns))) $$
        ("in" $$ nest 4 (ppExpr 0 p e))

ppAlt :: (a -> Doc) -> Alt a -> Doc
ppAlt p (pat,rhs) = lhs <+> "->" <+> ppExpr 0 p rhs
  where
    lhs = case pat of
        Default        -> "_"
        ConPat c ts as -> p c <+> sep [ "@" <+> ppType 1 p t | t <- ts ] <+> sep (map p as)
        LitPat i       -> integer i

ppType :: Int -> (a -> Doc) -> Type a -> Doc
ppType i p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> iff (i > 0) parens $ ppType 1 p t1 <+> "->" <+> ppType 0 p t2
    TyCon tc ts -> p tc <+> sep (map (ppType 1 p) ts)

iff :: Bool -> (a -> a) -> a -> a
iff True  f = f
iff False _ = id

