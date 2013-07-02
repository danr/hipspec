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
    hang (p nm <+> "=") 2 (ppExpr 0 p e)

ppExpr :: Int -> (a -> Doc) -> Expr a -> Doc
ppExpr i p e0 = case e0 of
    Var x ts -> iff (not (null ts) && i > 1) parens $
                     p x <> cat [ " @" <+> ppType 1 p t | t <- ts ]

    App{} -> iff (i > 1) parens $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 p) args
            pp_fun     = ppExpr 1 p fun
        in  hang pp_fun 2 (sep pp_args)
    Lit x         -> integer x
    String        -> "\"\""
    Lam{} -> iff (i > 0) parens $
        let (args,body) = collectBinders e0
            pp_args     = map p args
            pp_body     = ppExpr 0 p body
        in  hang ("\\" <+> sep pp_args <+> "->") 2 pp_body
    Case e x alts -> iff (i > 0) parens $
        hang ("case" <+> ppExpr 0 p e <+> "of" <+> p x <+> "{") 2
             (vcat (punctuate ";" (map (ppAlt p) alts))) !$ "}"
      where
        (!$) | length alts == 1 = (<+>)
             | otherwise        = ($$)

    Let fns e ->
        hang ("let" <+> "{") 2 (vcat (map (ppFun p) fns) <+> "}" <+> "in") $$
        ppExpr 0 p e

ppAlt :: (a -> Doc) -> Alt a -> Doc
ppAlt p (pat,rhs) = hang (lhs <+> "->") 2 (ppExpr 0 p rhs)
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

