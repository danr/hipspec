{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on how to
--   pretty-print variables.
module PrettySimple where

import Text.PrettyPrint.HughesPJ

import PrettyRich (parensIf,ppType)
import Simple

ppFun :: (a -> Doc) -> Function a -> Doc
ppFun p (Function nm tvs ty args e) =
    p nm <+> "::" <+>
        (if null tvs then empty else "forall" <+> sep (map p tvs) <+> ".")
        <+> ppType 0 p ty $$
    hang (p nm <+> sep (map p args) <+> "=") 2 (ppBody p e)

ppBody :: (a -> Doc) -> Body a -> Doc
ppBody p b = case b of
    Case e alts ->
        hang ("case" <+> ppExpr 0 p e <+> "of" <+> "{") 2
             (vcat (punctuate ";" (map (ppAlt p) alts))) !$ "}"
      where
        (!$) | length alts == 1 = (<+>)
             | otherwise        = ($$)
    Body e -> ppExpr 0 p e

ppAlt :: (a -> Doc) -> Alt a -> Doc
ppAlt p (pat,rhs) = hang (lhs <+> "->") 2 (ppBody p rhs)
  where
    lhs = case pat of
        Default        -> "_"
        ConPat c ts bs -> p c <+> sep [ "@" <+> ppType 1 p t | t <- ts ] <+> sep (map (p . fst) bs)
        LitPat i       -> integer i

ppExpr :: Int -> (a -> Doc) -> Expr a -> Doc
ppExpr i p e0 = case e0 of
    Lit x -> integer x

    Var x ts -> parensIf (not (null ts) && i > 1) $
        p x <> cat [ " @" <+> ppType 1 p t | t <- ts ]

    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 p) args
            pp_fun     = ppExpr 1 p fun
        in  hang pp_fun 2 (sep pp_args)

