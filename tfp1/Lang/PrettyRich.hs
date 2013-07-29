{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on how to
--   pretty-print variables.
module Lang.PrettyRich where

import Text.PrettyPrint

import Lang.Rich
import Lang.PrettyUtils
import Lang.Type

ppProg :: Kit a -> Program a -> Doc
ppProg k (Program _ds fs) = vcat (map (ppFun k) fs)

ppFun :: Kit a -> Function a -> Doc
ppFun k@(_,q) (Function nm e) = hang (q nm <+> "=") 2 (ppExpr 0 k e)

ppExpr :: Int -> Kit a -> Expr a -> Doc
ppExpr i k@(p,q) e0 = case e0 of
    Var x ts -> parensIf (not (null ts) && i > 1) $
        p x <> cat [ " @" <+> ppType 1 p t | t <- ts ]

    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 k) args
            pp_fun     = ppExpr 1 k fun
        in  hang pp_fun 2 (sep pp_args)
    Lit x _  -> integer x
    String{} -> "\"\""
    Lam{} -> parensIf (i > 0) $
        let (args,body) = collectBinders e0
            pp_body     = ppExpr 0 k body
            pp_args     = map q args
        in  hang ("\\" <+> sep pp_args <+> "->") 2 pp_body
    Case e x alts -> parensIf (i > 0) $
        hang ("case" <+> ppExpr 0 k e <+> "of" <+> maybe empty q x) 2
             (inside "{ " "; " "}" (map (ppAlt k) alts))
    Let fns e -> parensIf (i > 0) $
        hang ("let" <+> "{") 2 (vcat (map (ppFun k) fns) <+> "}" <+> "in") $$
        ppExpr 0 k e

ppAlt :: Kit a -> Alt a -> Doc
ppAlt k (pat,rhs) = hang (ppPat k pat <+> "->") 2 (ppExpr 0 k rhs)

ppPat :: Kit a -> Pattern a -> Doc
ppPat (p,q) pat = case pat of
    Default        -> "_"
    ConPat c ts bs -> hang (p c) 2 (sep ([ "@" <+> ppType 1 p t | t <- ts ] ++ map q bs))
    LitPat i _     -> integer i

ppType :: Int -> (a -> Doc) -> Type a -> Doc
ppType i p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> parensIf (i > 0) $ hang (ppType 1 p t1 <+> "->") 2 (ppType 0 p t2)
    TyCon tc ts -> hang (p tc) 2 (sep (map (ppType 1 p) ts))
    Star        -> "*"
    Forall{}    -> parensIf (i > 0) $
        let (tvs,t) = collectForalls t0
        in  hang ("forall" <+> sep (map p tvs) <+> ".") 2 (ppType 0 p t)

ppTyped :: (a -> Doc) -> Typed a -> Doc
ppTyped p (x ::: t) = hang (p x <+> "::") 2 (ppType 0 p t)

