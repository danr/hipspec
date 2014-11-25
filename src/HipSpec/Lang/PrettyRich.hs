{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the rich language, parameterised on whether to print
--   types of variables.
module HipSpec.Lang.PrettyRich where

import Text.PrettyPrint

import HipSpec.Lang.Rich
import HipSpec.Lang.PrettyUtils
import HipSpec.Lang.Type

ppProg :: Types -> P a -> Program a -> Doc
ppProg t p (Program _ds fs) = vcat (map (ppFun t p) fs)

ppFun :: Types -> P a -> Function a -> Doc
ppFun t p (Function f ty e) = ppId f ty <+> "=" $\ ppExpr 0 t p e
  where
    ppId x t' = ppTyped t (p x) (ppPolyType p t')

ppExpr :: Int -> Types -> P a -> Expr a -> Doc
ppExpr i t p e0 = case e0 of
    Lcl x ty    -> ppId x ty
    Gbl x ty ts -> parensIf (not (null ts) && i > 1) $
        --"*" <> ppPolyId x ty $\ sep [ "@" <+> ppType 2 p t' | t' <- ts ]
        ppPolyId x ty
    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 t p) args
            pp_fun     = ppExpr 1 t p fun
        in  pp_fun $\ (sep pp_args)
    Lit x    -> integer x
    String s -> text (show s)
    Lam{} -> parensIf (i > 0) $
        let (args,body) = collectBinders e0
            pp_body     = ppExpr 0 t p body
            pp_args     = map (uncurry ppId) args
        in  "\\" <+> sep pp_args <+> "->" $\ pp_body
    Case e s alts -> parensIf (i > 0) $
        "case" <+> ppExpr 0 t p e <+> "of" <+> maybe empty (uncurry ppId) s $\
        inside "{ " "; " "}" (map (ppAlt t p) alts)
    Let fns e -> parensIf (i > 0) $
        ("let" <+> "{" $\ vcat (map (ppFun t p) fns) <+> "}" <+> "in") $$
        ppExpr 0 t p e
  where
    ppId     x ty = ppTyped t (p x) (ppType 0 p ty)
    ppPolyId x ty = ppTyped t (p x) (ppPolyType p ty)

ppAlt :: Types -> P a -> Alt a -> Doc
ppAlt t p (pat,rhs) = ppPat t p pat <+> "->" $\ ppExpr 0 t p rhs

ppPat :: Types -> P a -> Pattern a -> Doc
ppPat t p pat = case pat of
    Default           -> "_"
    ConPat c ty ts bs ->
        ppPolyId c ty $\
        sep (
    --        ([ "@" <+> ppType 1 p t' | t' <- ts ] ++
        map (uncurry ppId) bs)
    LitPat i          -> integer i
  where
    ppId     x ty = ppTyped t (p x) (ppType 0 p ty)
    ppPolyId x ty = ppTyped t (p x) (ppPolyType p ty)

ppPolyType :: P a -> PolyType a -> Doc
ppPolyType p (Forall [] ty) = ppType 0 p ty
ppPolyType p (Forall xs ty) = "forall" <+> sep (map p xs) <+> "." $\ ppType 0 p ty

ppType :: Int -> P a -> Type a -> Doc
ppType i p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> parensIf (i > 0) $ ppType 1 p t1 <+> "->" $\ ppType 0 p t2
    TyCon tc ts -> parensIf (i > 1) $ p tc $\ sep (map (ppType 1 p) ts)
    Integer     -> "Integer"

