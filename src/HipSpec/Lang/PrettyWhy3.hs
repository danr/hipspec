{-# LANGUAGE OverloadedStrings,PatternGuards #-}
-- Almost the same as PrettyAltErgo
module HipSpec.Lang.PrettyWhy3 where

import Text.PrettyPrint

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.PrettyUtils

import Control.Monad
import Data.List

type Id a = a -> Doc

prime :: Doc -> Doc
prime d = "\'" <> d

why3Keywords :: [String]
why3Keywords = words $ unwords $
    [ "not"
    , "if then else let in match with end as true false forall exists"
    , "theory type constant function predicate inductive coinductive"
    , "axiom lemma goal use clone namespace import"
    ]

alphabet :: [String]
alphabet = (\\ why3Keywords) $ do
    n <- [1..]
    replicateM n ['a'..'z']

commasep,commasepP :: [Doc] -> Doc
commasep = sep . punctuate ","

commasepP xs | length xs >= 2 = parens (commasep xs)
             | otherwise      = commasep xs

ppClauses :: Id a -> [Clause a] -> Doc
ppClauses p = theory . vcat . zipWith (ppClause p) alphabet
  where
    theory d = hang ("theory" <+> "Why") 2 d $$ "end"

ppClause :: Id a -> String -> Clause a -> Doc
ppClause p name cls = case cls of
    SortSig x n -> "type" <+> p x <+> sep (map (prime . text) (take n alphabet))

    TypeSig x _tvs args res -> hang "function" 2 (ppTySig p x args res)

    Clause _ cl _tvs phi -> hang (ppClType cl <+> text name <+> ":") 2 (ppForm p phi)

    Comment s            -> hang "(*" 2 (vcat (map text (lines s)) <+> "*)")

ppClType :: ClType -> Doc
ppClType cl = case cl of
    Axiom -> "axiom"
    Goal  -> "goal"

ppTySig :: Id a -> a -> [Type a] -> Type a -> Doc
ppTySig p x args res
    = hang (p x) 2
    $ hang (sep (map (ppType p) args)) 2
    $ ":" <+> ppType p res

ppType :: Id a -> Type a -> Doc
ppType p = go
  where
    go t0 = case t0 of
        TyCon tc [] -> p tc
        TyCon tc ts -> parens (hang (p tc) 2 (sep (map go ts)))
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
    And     -> " /\\ "
    Or      -> " \\/ "
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
        Apply f ts [] -> p f <+> commentTys ts
        Apply f ts as -> parens (hang (p f <+> commentTys ts) 2 (sep (map go as)))
        Var v         -> p v
        Lit x         -> integer x
        Sig tm ty     -> parens (hang (go tm <+> ":") 2 (ppType p ty))

    commentTys = comment' . sep . punctuate comma . map (ppType p)

    comment' d = "(*" <+> d <+> "*)"

