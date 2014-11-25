{-# LANGUAGE OverloadedStrings,RecordWildCards,PatternGuards #-}
-- | Pretty-printing the rich language, parameterised on whether to print
--   types of variables.
module HipSpec.Lang.PrettyRich where

import Text.PrettyPrint

import HipSpec.Lang.Rich
import HipSpec.Lang.PrettyUtils
import HipSpec.Lang.Type

ppProg :: Types -> P a -> Program a -> Doc
ppProg t pk (Program _ds fs) = vcat (map (ppFun t pk) fs)

ppFun :: Types -> P a -> Function a -> Doc
ppFun t pk (Function f ty e) = ppId f ty <+> "=" $\ ppExpr 0 t pk e
  where
    PK{..} = pk
    ppId x t' = ppTyped t (p x) (ppPolyType pk t')

ppExpr :: Int -> Types -> P a -> Expr a -> Doc
ppExpr i t pk e0 = case e0 of
    Lcl x ty    -> parensIf (pp_infix x) (ppId x ty)
    Gbl x ty ts -> parensIf (not (null ts) && i > 2 || pp_infix x) $
        --"*" <> ppPolyId x ty $\ sep [ "@" <+> ppType 2 pk t' | t' <- ts ]
        ppPolyId x ty
    App{} | (Gbl x _ _,[e1,Lam y _t e2]) <- collectArgs e0, pp_infix x ->
        parensIf (i > 1) $ sep [ppExpr 1 t pk e1 $\ (p x $\ "\\" <+> p y <+> "->"), ppExpr 1 t pk e2]
    App{} | (Gbl x _ _,[e1,e2]) <- collectArgs e0, pp_infix x ->
        parensIf (i > 1) $ sep [ppExpr 2 t pk e1 $\ p x, ppExpr 2 t pk e2]
    App{} -> parensIf (i > 1) $
        let (fun,args) = collectArgs e0
            pp_args    = map (ppExpr 2 t pk) args
            pp_fun     = ppExpr 1 t pk fun
        in  pp_fun $\ (sep pp_args)
    Lit x    -> integer x
    String s -> text (show s)
    Lam{} -> parensIf (i > 0) $
        let (args,body) = collectBinders e0
            pp_body     = ppExpr 0 t pk body
            pp_args     = map (uncurry ppId) args
        in  "\\" <+> sep pp_args <+> "->" $\ pp_body
    Case e s alts -> parensIf (i > 0) $
        "case" <+> ppExpr 0 t pk e <+> "of" <+> maybe empty (uncurry ppId) s $\
        inside "{ " "; " "}" (map (ppAlt t pk) alts)
    Let fns e -> parensIf (i > 0) $
        ("let" <+> "{" $\ vcat (map (ppFun t pk) fns) <+> "}" <+> "in") $$
        ppExpr 0 t pk e
  where
    PK{..} = pk
    ppId     x ty = ppTyped t (p x) (ppType 0 pk ty)
    ppPolyId x ty = ppTyped t (p x) (ppPolyType pk ty)

ppAlt :: Types -> P a -> Alt a -> Doc
ppAlt t pk (pat,rhs) = ppPat t pk pat <+> "->" $\ ppExpr 0 t pk rhs

ppPat :: Types -> P a -> Pattern a -> Doc
ppPat t pk pat = case pat of
    Default           -> "_"
    ConPat c ty ts bs ->
        ppPolyId c ty $\
        sep (
    --        ([ "@" <+> ppType 1 pk t' | t' <- ts ] ++
        map (uncurry ppId) bs)
    LitPat i          -> integer i
  where
    PK{..} = pk
    ppId     x ty = ppTyped t (parensIf (pp_infix x) (p x)) (ppType 0 pk ty)
    ppPolyId x ty = ppTyped t (parensIf (pp_infix x) (p x)) (ppPolyType pk ty)

ppPolyType :: P a -> PolyType a -> Doc
ppPolyType pk (Forall [] ty) = ppType 0 pk ty
ppPolyType pk (Forall xs ty) = "forall" <+> sep (map p xs) <+> "." $\ ppType 0 pk ty
  where
    PK{..} = pk

ppType :: Int -> P a -> Type a -> Doc
ppType i pk t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> parensIf (i > 0) $ ppType 1 pk t1 <+> "->" $\ ppType 0 pk t2
    TyCon tc ts -> parensIf (i > 1) $ p tc $\ sep (map (ppType 1 pk) ts)
    Integer     -> "Integer"
  where
    PK{..} = pk

