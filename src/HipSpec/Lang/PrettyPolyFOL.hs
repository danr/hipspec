{-# LANGUAGE OverloadedStrings,PatternGuards #-}
module HipSpec.Lang.PrettyPolyFOL where

import Text.PrettyPrint

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.PrettyUtils

ppClause :: PP a b -> Clause a b -> Doc
ppClause p cls = case cls of
    SortSig x n            -> tff [pp_symb p x,"type",ppTySig p (pp_symb p x) [] (replicate n TType) TType]
    TypeSig x tvs args res -> tff [pp_symb p x,"type",ppTySig p (pp_symb p x) tvs args res]
    Clause _ _ cl tvs phi  -> tff ["x",ppClType cl,ppTyQuant p tvs (ppForm p phi)]
    Comment s              -> vcat (map (\ l -> "%" <+> text l) (lines s))
  where
    tff xs = "tff" <> csv xs <> "."

ppClType :: ClType -> Doc
ppClType cl = case cl of
    Axiom -> "axiom"
    Goal  -> "conjecture"

ppTySig :: PP a b -> Doc -> [b] -> [Type a b] -> Type a b -> Doc
ppTySig p x tvs args res = hang (x <+> ":") 2 (ppTopType p tvs args res)

ppTyQuant :: PP a b -> [b] -> Doc -> Doc
ppTyQuant p xs = ppQuant p "!>" (zip xs (repeat TType))

ppQuant :: PP a b -> Doc -> [(b,Type a b)] -> Doc -> Doc
ppQuant p q xs d = case xs of
    [] -> d
    _  -> hang (q <> bsv [ ppTySig p (pp_var p x) [] [] t | (x,t) <- xs] <> ":") 2 d
  where
    bsv = inside "[" "," "]"

ppTopType :: PP a b -> [b] -> [Type a b] -> Type a b -> Doc
ppTopType p tvs args res = ppTyQuant p tvs (pp_args (ppType p res))
  where
    pp_args = case args of
        []  -> id
        [x] -> hang (ppType p x <+> ">") 2
        xs  -> hang (starsep (map (ppType p) xs) <+> ">") 2

ppType :: PP a b -> Type a b -> Doc
ppType p = go
  where
    go t0 = case t0 of
        TyCon tc ts -> pp_symb p tc <> csv (map go ts)
        TyVar x     -> pp_var p x
        TType       -> "$tType"
        Integer     -> "$int"

ppForm :: PP a b -> Formula a b -> Doc
ppForm p f0 = case f0 of
    _ | Just (op,fs) <- collectFOp f0 -> inside "(" (ppFOp op) ")" (map (ppForm p) fs)
      | Just (q,(bs,f)) <- collectQ f0 -> ppQuant p (ppQ q) bs (ppForm p f)
    TOp top t1 t2 -> sep [ppTerm p t1 <+> ppTOp top,ppTerm p t2]
    Neg f         -> "~" <+> ppForm p f
--    Pred q fs     -> p q <> csv (map (ppForm p) fs)
    FOp{} -> error "PrettyPolyFOL.ppForm FOp"
    Q{}   -> error "PrettyPolyFOL.ppForm Q"

ppQ :: Q -> Doc
ppQ q = case q of
    Forall -> "!"
    Exists -> "?"

ppFOp :: FOp -> Doc
ppFOp op = case op of
    And     -> " & "
    Or      -> " | "
    Implies -> " => "
    Equiv   -> " <=> "

ppTOp :: TOp -> Doc
ppTOp op = case op of
    Equal   -> "="
    Unequal -> "!="

ppTerm :: PP a b -> Term a b -> Doc
ppTerm p = go
  where
    go tm0 = case tm0 of
        Apply f ts as -> pp_symb p f <> csv (map (ppType p) ts ++ map go as)
        Var v         -> pp_var p v
        Lit x         -> integer x

