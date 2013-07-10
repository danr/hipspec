{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the functional language, parameterised on how to
--   pretty-print variables.
module PrettyFO where

import Text.PrettyPrint

import FunctionalFO

import Type
import PrettyUtils

ppFun :: (a -> Doc) -> Function a -> Doc
ppFun p (Function nm as e) = hang (p nm <+> csv (map p as) <+> "=") 2 (ppBody p e)

ppBody :: (a -> Doc) -> Body a -> Doc
ppBody p b0 = case b0 of
    Case e alts -> hang ("case" <+> ppExpr p e <+> "of") 2
        (inside "{ " "; " "}" (map (ppAlt p) alts))
    Body e -> ppExpr p e

ppExpr :: (a -> Doc) -> Expr a -> Doc
ppExpr p e0 = case e0 of
    Apply f tys args -> hang (p f) 2 (ppTysArgs p tys (map (ppExpr p) args))
    Lit x _          -> integer x

ppAlt :: (a -> Doc) -> Alt a -> Doc
ppAlt p (pat,rhs) = hang (ppPat p pat <+> "->") 2 (ppBody p rhs)

ppTysArgs :: (a -> Doc) -> [FOType a] -> [Doc] -> Doc
ppTysArgs _ []  []      = empty
ppTysArgs p tys pp_args = csv $ pp_tys ++ pp_args
  where
    pp_tys  = [ "@" <+> ppFOType p t | t <- tys ]

ppPat :: (a -> Doc) -> Pattern a -> Doc
ppPat p pat = case pat of
    Default           -> "_"
    ConPat c tys args -> hang (p c) 2 (ppTysArgs p tys (map p args))
    LitPat i _        -> integer i

ppFOType :: (a -> Doc) -> FOType a -> Doc
ppFOType p (FOType tvs args res) = pp_forall $ pp_args $ pp_res
  where
    pp_forall = case tvs of
        [] -> id
        _  -> hang ("forall" <+> sep (map p tvs) <+> ".") 2

    pp_args = case args of
        [] -> id
        _  -> \ r -> csv (map (ppType p) args) <+> "->" <+> r

    pp_res = ppType p res

ppType :: (a -> Doc) -> Type a -> Doc
ppType p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> "Fn" <+> csv (map (ppType p) [t1,t2])
    TyCon tc ts -> p tc <+> csv (map (ppType p) ts)
    Star        -> "*"
    Forall{}    -> error "PrettyFO.ppType: forall in inner FO"

