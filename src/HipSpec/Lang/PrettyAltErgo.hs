{-# LANGUAGE OverloadedStrings,PatternGuards #-}
module HipSpec.Lang.PrettyAltErgo where

import Text.PrettyPrint

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.PrettyUtils

import Control.Monad

prime :: Doc -> Doc
prime d = "\'" <> d

alphabet :: [String]
alphabet = do
    n <- [1..]
    replicateM n ['a'..'z']

commasep,commasepP :: [Doc] -> Doc
commasep = sep . punctuate ","

commasepP xs | length xs >= 2 = parens (commasep xs)
             | otherwise      = commasep xs

ppClause :: PP a b -> Clause a b -> Doc
ppClause p cls = case cls of
    SortSig x n
        -> "type" <+> commasepP (map (prime . text) (take n alphabet)) <+> pp_symb p x

    TypeSig x _tvs args res -> hang "logic" 2 (ppTySig p (pp_symb p x) args res)

    Clause name _trg cl _tvs phi -> hang (ppClType cl <+> "_" <> nm <+> ":") 2 (ppForm p phi)
      where
        nm = maybe empty int name

    Comment s            -> hang "(*" 2 (vcat (map text (lines s)) <+> "*)")

ppClType :: ClType -> Doc
ppClType cl = case cl of
    Axiom -> "axiom"
    Goal  -> "goal"

ppTySig :: PP a b -> Doc -> [Type a b] -> Type a b -> Doc
ppTySig p x args res
    = hang (x <+> ":") 2 (pp_args (ppType p res))
  where
    pp_args = case args of
        [] -> id
        _  -> hang (commasep (map (ppType p) args) <+> "->") 2

ppType :: PP a b -> Type a b -> Doc
ppType p = go
  where
    go t0 = case t0 of
        TyCon tc ts -> commasepP (map go ts) <+> pp_symb p tc
        TyVar x     -> prime (pp_var p x)
        TType       -> error "PrettyAltErgo.ppType: TType"
        Integer     -> "int"

ppForm :: PP a b -> Formula a b -> Doc
ppForm p f0 = case f0 of
    _ | Just (op,fs) <- collectFOp f0 -> inside "(" (ppFOp op) ")" (map (ppForm p) fs)
    Q q x t f         -> hang (ppQ q <+> ppTySig p (pp_var p x) [] t <+> ".") 2 (ppForm p f)
    TOp op t1 t2      -> sep [ppTerm p t1 <+> ppTOp op,ppTerm p t2]
    Neg f             -> "not" <+> parens (ppForm p f)
--    Pred q fs         -> pp_symb p q <> csv (map (ppForm p) fs)
    FOp{}             -> error "PrettyAltErgo.ppForm: FOp"
    DataDecl _ fm     -> ppForm p fm

ppQ :: Q -> Doc
ppQ q = case q of
    Forall -> "forall"
    Exists -> "exists"

ppFOp :: FOp -> Doc
ppFOp op = case op of
    And     -> " and "
    Or      -> " or "
    Implies -> " -> "
    Equiv   -> " <-> "

ppTOp :: TOp -> Doc
ppTOp op = case op of
    Equal   -> "="
    Unequal -> "<>"

ppTerm :: PP a b -> Term a b -> Doc
ppTerm p = go
  where
    go tm0 = case tm0 of
        Apply f ts as -> pp_symb p f <> ("(*" <+> csv (map (ppType p) ts) <+> "*)") <> csv (map go as)
        Var v         -> pp_var p v
        Lit x         -> integer x

