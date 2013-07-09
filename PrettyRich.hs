{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on how to
--   pretty-print variables.
module PrettyRich where

import Text.PrettyPrint

import Rich
import PrettyUtils
import PrettyType

ppProg :: (a -> Doc) -> Program a -> Doc
ppProg p (Program _ds fs) = vcat (map (ppFun p) fs)

ppFun :: (a -> Doc) -> Function a -> Doc
ppFun p (Function nm e) = hang (p nm <+> "=") 2 (ppExpr 0 p e)

ppExpr :: Int -> (a -> Doc) -> Expr a -> Doc
ppExpr i p e0 = case e0 of
    Var x ts -> parensIf (not (null ts) && i > 1) $
        p x <> cat [ " @" <+> ppType 1 p t | t <- ts ]

    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 p) args
            pp_fun     = ppExpr 1 p fun
        in  hang pp_fun 2 (sep pp_args)
    Lit x _       -> integer x
    String{}      -> "\"\""
    Lam{} -> parensIf (i > 0) $
        let (args,body) = collectBinders e0
            pp_body     = ppExpr 0 p body
            pp_args     = map p args
        in  hang ("\\" <+> sep pp_args <+> "->") 2 pp_body
    Case e x alts -> parensIf (i > 0) $
        hang ("case" <+> ppExpr 0 p e <+> "of" <+> maybe empty p x <+> "{") 2
             (vcat (punctuate ";" (map (ppAlt p) alts))) !$ "}"
      where
        (!$) | length alts == 1 = (<+>)
             | otherwise        = ($$)

    Let fns e -> parensIf (i > 0) $
        hang ("let" <+> "{") 2 (vcat (map (ppFun p) fns) <+> "}" <+> "in") $$
        ppExpr 0 p e

ppAlt :: (a -> Doc) -> Alt a -> Doc
ppAlt p (pat,rhs) = hang (ppPat p pat <+> "->") 2 (ppExpr 0 p rhs)

ppPat :: (a -> Doc) -> Pattern a -> Doc
ppPat p pat = case pat of
    Default        -> "_"
    ConPat c ts bs -> p c <+> sep [ "@" <+> ppType 1 p t | t <- ts ]
                          <+> sep (map p bs)
    LitPat i _     -> integer i

