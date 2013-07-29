{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the functional language, parameterised on how to
--   pretty-print variables.
module HipSpec.Lang.PrettyFO where

import Text.PrettyPrint

import HipSpec.Lang.FunctionalFO

import HipSpec.Lang.Type hiding ((:::))
import HipSpec.Lang.PrettyUtils

type Id a = a -> Doc

ppFun :: Id a -> Function a -> Doc
ppFun p (Function f tvs args res b) =
    hang (p f <+> "::") 2 pp_type $$
    hang (p f) 2 (hang (csv (map (p . fst) args) <+> "=") 2 (ppBody p b))
  where
    -- | Pretty printing the type
    pp_type = pp_forall (pp_args pp_res)

    pp_forall = case tvs of
        [] -> id
        _  -> hang ("forall" <+> sep (map p tvs) <+> ".") 2

    pp_args = case map snd args of
        [] -> id
        as -> \ r -> hang (csv (map (ppType p) as) <+> "->") 2 r

    pp_res = ppType p res

ppBody :: Id a -> Body a -> Doc
ppBody p b0 = case b0 of
    Case e alts -> hang ("case" <+> ppExpr p e <+> "of") 2
        (inside "{ " "; " "}" (map (ppAlt p) alts))
    Body e -> ppExpr p e

ppAlt :: Id a -> Alt a -> Doc
ppAlt p (pat,rhs) = hang (ppPat p pat <+> "->") 2 (ppBody p rhs)

ppPat :: Id a -> Pattern a -> Doc
ppPat p pat = case pat of
    Default           -> "_"
    ConPat c tys args -> hang (p c) 2 (ppTysArgs p tys (map (ppTyped p) args))
    LitPat i          -> integer i

ppTyped :: Id a -> (a,Type a) -> Doc
ppTyped p (x,t) = hang (p x <+> "::") 2 (ppType p t)

ppExpr :: Id a -> Expr a -> Doc
ppExpr p e0 = case e0 of
    App t1 t2 e1 e2 -> hang "app" 2 (ppTysArgs p [t1,t2] (map (ppExpr p) [e1,e2]))
    Fun f tys args  -> hang (p f) 2 (ppTysArgs p tys (map (ppExpr p) args))
    Ptr f tys       -> hang (p f <> "_ptr") 2 (ppTysArgs p tys [])
    Lit x           -> integer x

ppTysArgs :: (a -> Doc) -> [Type a] -> [Doc] -> Doc
ppTysArgs _ []  []      = empty
ppTysArgs p tys pp_args = csv $ pp_tys ++ pp_args
  where
    pp_tys  = [ "@" <+> ppType p t | t <- tys ]

ppType :: (a -> Doc) -> Type a -> Doc
ppType p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> hang "Fn" 2 (csv (map (ppType p) [t1,t2]))
    TyCon tc ts -> hang (p tc) 2 (csv (map (ppType p) ts))
    Star        -> error "PrettyFO.ppType: star"
    Forall{}    -> error "PrettyFO.ppType: forall"

