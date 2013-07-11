{-# LANGUAGE OverloadedStrings #-}
-- | Pretty-printing the functional language, parameterised on how to
--   pretty-print variables.
module PrettyFO where

import Text.PrettyPrint

import FunctionalFO

import Type hiding ((:::))
import PrettyUtils

ppFun :: Kit a -> Function a -> Doc
ppFun k@(p,q) (Function nm as e)
    = hang (q nm) 2 $ hang (csv (map p as) <+> "=") 2 (ppBody k e)

ppBody :: Kit a -> Body a -> Doc
ppBody k b0 = case b0 of
    Case e alts -> hang ("case" <+> ppExpr k e <+> "of") 2
        (inside "{ " "; " "}" (map (ppAlt k) alts))
    Body e -> ppExpr k e

ppExpr :: Kit a -> Expr a -> Doc
ppExpr k@(p,_) e0 = case e0 of
    Apply f tys args -> hang (p f) 2 (ppTysArgs p tys (map (ppExpr k) args))
    Lit x _          -> integer x

ppAlt :: Kit a -> Alt a -> Doc
ppAlt k (pat,rhs) = hang (ppPat k pat <+> "->") 2 (ppBody k rhs)

ppTysArgs :: (a -> Doc) -> [FOType a] -> [Doc] -> Doc
ppTysArgs _ []  []      = empty
ppTysArgs p tys pp_args = csv $ pp_tys ++ pp_args
  where
    pp_tys  = [ "@" <+> ppFOType p t | t <- tys ]

ppPat :: Kit a -> Pattern a -> Doc
ppPat (p,q) pat = case pat of
    Default           -> "_"
    ConPat c tys args -> hang (p c) 2 (ppTysArgs p tys (map q args))
    LitPat i _        -> integer i

ppFOTyped :: (a -> Doc) -> FOTyped a -> Doc
ppFOTyped p (x ::: t) = hang (p x <+> "::") 2 (ppFOType p t)

ppFOType :: (a -> Doc) -> FOType a -> Doc
ppFOType p (FOType tvs args res) = pp_forall $ pp_args $ pp_res
  where
    pp_forall = case tvs of
        [] -> id
        _  -> hang ("forall" <+> sep (map p tvs) <+> ".") 2

    pp_args = case args of
        [] -> id
        _  -> \ r -> hang (csv (map (ppType p) args) <+> "->") 2 r

    pp_res = ppType p res

ppType :: (a -> Doc) -> Type a -> Doc
ppType p t0 = case t0 of
    TyVar x     -> p x
    ArrTy t1 t2 -> hang "Fn" 2 (csv (map (ppType p) [t1,t2]))
    TyCon tc ts -> hang (p tc) 2 (csv (map (ppType p) ts))
    Star        -> "*"
    Forall{}    -> error "PrettyFO.ppType: forall in inner FO"

