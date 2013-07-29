{-# LANGUAGE OverloadedStrings,PatternGuards #-}
module Lang.PrettyAltErgo where

import Text.PrettyPrint

import Lang.PolyFOL
import Lang.PrettyUtils

import Control.Monad

type Id a = a -> Doc

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

ppClause :: Id a -> Clause a -> Doc
ppClause p cls = case cls of
    SortSig x n
        -> "type" <+> commasepP (map (prime . text) (take n alphabet)) <+> p x

    TypeSig x _tvs args res -> hang "logic" 2 (ppTySig p x args res)

    Clause _ cl _tvs phi -> hang (ppClType cl <+> "_" <+> ":") 2 (ppForm p phi)

    Comment s            -> hang "(*" 2 (vcat (map text (lines s)) <+> "*)")

ppClType :: ClType -> Doc
ppClType cl = case cl of
    Axiom -> "axiom"
    Goal  -> "goal"

ppTySig :: Id a -> a -> [Type a] -> Type a -> Doc
ppTySig p x args res
    = hang (p x <+> ":") 2 (pp_args (ppType p res))
  where
    pp_args = case args of
        [] -> id
        _  -> hang (commasep (map (ppType p) args) <+> "->") 2

ppType :: Id a -> Type a -> Doc
ppType p = go
  where
    go t0 = case t0 of
        TyCon tc ts -> commasepP (map go ts) <+> p tc
        TyVar x     -> prime (p x)
        TType       -> error "PrettyAltErgo.ppType: TType"

ppForm :: Id a -> Formula a -> Doc
ppForm p f0 = case f0 of
    _ | Just (op,fs) <- collectFOp f0 -> inside "(" (ppFOp op) ")" (map (ppForm p) fs)
    Q q x t f         -> hang (ppQ q <+> ppTySig p x [] t <+> ".") 2 (ppForm p f)
    TOp op t1 t2      -> sep [ppTerm p t1 <+> ppTOp op,ppTerm p t2]
    Neg f             -> "not" <+> parens (ppForm p f)
    Pred q fs         -> p q <> csv (map (ppForm p) fs)
    FOp{}             -> error "PrettyAltErgo.ppForm: FOp"

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

ppTerm :: Id a -> Term a -> Doc
ppTerm p = go
  where
    go tm0 = case tm0 of
        Apply f _ts as -> p f <> csv (map go as)
        Var v          -> p v
        Lit x          -> integer x

