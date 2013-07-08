{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on how to
--   pretty-print variables.
module PrettySimple where

import Text.PrettyPrint.HughesPJ

import PrettyRich (ppPat)
import PrettyUtils
import PrettyType
import Simple

ppFun :: (a -> Doc) -> Function a -> Doc
ppFun p (Function nm args e) =
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
ppAlt p (pat,rhs) = hang (ppPat p pat <+> "->") 2 (ppBody p rhs)

ppExpr :: Int -> (a -> Doc) -> Expr a -> Doc
ppExpr i p e0 = case e0 of
    Lit x _ -> integer x

    Var x ts -> parensIf (not (null ts) && i > 1) $
        p x <> cat [ " @" <+> ppType 1 p t | t <- ts ]

    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 p) args
            pp_fun     = ppExpr 1 p fun
        in  hang pp_fun 2 (sep pp_args)

