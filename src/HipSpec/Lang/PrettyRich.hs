{-# LANGUAGE OverloadedStrings,RecordWildCards,PatternGuards #-}
-- | Pretty-printing the rich language, parameterised on whether to print
--   types of variables.
module HipSpec.Lang.PrettyRich where

import Text.PrettyPrint

import HipSpec.Lang.Rich
import HipSpec.Lang.PrettyUtils
import HipSpec.Lang.Type

ppProg :: Types -> P a -> Program a -> Doc
ppProg t pk (Program ds fs) = vcat (map (ppData pk) ds ++ map (ppFun t pk) fs)

ppInst :: P a -> Instance a -> Doc
ppInst pk (Instance ctx hd assoc fns) =
    ((("instance" $\ pp_ctx) $\ ppType 0 pk hd) $\ "where") $\
        vcat (map pp_assoc assoc ++ map (ppFun Don'tShow pk) fns)
  where
    PK{..} = pk
    pp_ctx
        | null ctx = empty
        | otherwise = inside "(" "," ")" (map (ppType 0 pk) ctx) <+> "=>"

    pp_assoc (a,b,c) = ("type" <+> p a <+> ppType 2 pk b <+> "=") $\ ppType 0 pk c

ppData :: P a -> Datatype a -> Doc
ppData pk (Datatype tc tvs cons insts) =
    (d_or_n $\ (p tc $\ sep (map p tvs)) <+> "=") $\ sepWith "|"
        [ p c $\ sep (map (ppType 2 pk) args)
        | Constructor c args <- cons
        ]
        $\ pp_insts
  where
    d_or_n
        | [Constructor _ [_]] <- cons = "newtype"
        | otherwise = "data"
    PK{..} = pk
    pp_insts
        | null insts = empty
        | otherwise  = "deriving" $\ csv (map (ppType 0 pk) insts)

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
    ListLit [] -> text "[]"
    ListLit es -> inside "[ " ", " "]" (map (ppExpr 0 t pk) es)

    Do [] e -> ppExpr i t pk e
    Do ss e -> parensIf (i > 0) $ "do" <+> inside "{ " "; " "}" (map (ppStmt t pk) (ss ++ [StmtExpr e]))
  where
    PK{..} = pk
    ppId     x ty = ppTyped t (p x) (ppType 0 pk ty)
    ppPolyId x ty = ppTyped t (p x) (ppPolyType pk ty)

ppStmt :: Types -> P a -> Stmt a -> Doc
ppStmt t pk (StmtExpr e)      = ppExpr 0 t pk e
ppStmt t pk (BindExpr x mt e) =
  maybe
    id
    (\ t r -> r <+> "::" $\ ppType 0 pk t)
    mt
    (p pk x)
      <+> "<-" $\ ppExpr 0 t pk e

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
    TyCon tc ts -> parensIf (i > 1 && not (null ts)) $ p tc $\ sep (map (ppType 2 pk) ts)
    Integer     -> "Integer"
  where
    PK{..} = pk

