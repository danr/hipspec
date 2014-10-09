{-# LANGUAGE OverloadedStrings,PatternGuards #-}
module HipSpec.Lang.PrettySMT where

import Text.PrettyPrint

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.PrettyUtils

import Control.Monad

ppClause :: PP a b -> Clause a b -> Doc
ppClause p cls = case cls of
    SortSig x _n            -> parens ("declare-sort" $\ pp_symb p x)
    TypeSig x _tvs args res -> parens ("declare-fun" $\ sep
                                        [pp_symb p x
                                        ,parens (sep (map (ppType p) args))
                                        ,ppType p res])
    Clause _ _ _ _ (DataDecl ds _) -> ppDataDecls p ds
    Clause _ _ cl _tvs fm   -> parens ("assert" $\
                                        ppForm p
                                            (case cl of {Goal -> neg
                                                        ; _ -> id} $ fm))
    Comment s               -> vcat (map (\ l -> ";" <+> text l) (lines s))

ppDataDecls :: PP a b -> [DataDecl a b] -> Doc
ppDataDecls _ [] = empty
ppDataDecls p ds = parens ("declare-datatypes" <+> parens empty $\ parens (sep (map data_decl ds)))
  where
    data_decl (Data tc _ cons) = parens (pp_symb p tc $\ sep (map con_decl cons))
    --con_decl (con,[])   = pp_symb p con -- CVC4 cannot handle this
    con_decl (con,args) = parens
        (pp_symb p con $\ sep [ parens (pp_symb p v <+> ppType p t) | (v,t) <- args ])

ppType :: PP a b -> Type a b -> Doc
ppType p = go
  where
    go t0 = case t0 of
        TyCon tc ts -> pp_symb p tc <> csv (map go ts)
        TyVar x     -> pp_var p x
        TType       -> "*"
        Integer     -> "Int"

ppForm :: PP a b -> Formula a b -> Doc
ppForm p f0 = case f0 of
    _ | Just (op,fs) <- collectFOp f0  -> parens (ppFOp op $\ sep (map (ppForm p) fs))
    Q q bs trg qid tmid f ->
      parens (ppQ q $\ sep
        [ppQList p bs
        ,ppKVs (zmap (ppTrg p) trg ++ zmap ppQid qid ++ zmap (ppTmId p) tmid) (ppForm p f)
        ])
    f `Named` s   -> ppKVs [(k,text s) | k <- ["named","lblpos","lblneg"]] (ppForm p f)
    f `TermNamed` tm -> ppKVs [(k,bracketed (ppTerm p tm)) | k <- ["named","lblpos","lblneg"]] (ppForm p f)
    TOp top t1 t2 -> parens (ppTOp top $\ sep (map (ppTerm p) [t1,t2]))
    Neg f         -> parens ("not" $\ ppForm p f)
--    Pred q fs     -> p q <> csv (map (ppForm p) fs)
    DataDecl _ fm -> ppForm p fm
    FOp{} -> error "PrettySMT.ppForm FOp"

piped :: Doc -> Doc
piped d = "|" <> d <> "|"

bracketed :: Doc -> Doc
bracketed d = "|{" <> d <> "}|"

ppKVs :: [(Doc,Doc)] -> Doc -> Doc
ppKVs []  d = d
ppKVs kvs d = parens ("!" $\ sep (d:[ (char ':' <> k) $\ v | (k,v) <- kvs ]))

ppTrg :: PP a b -> Trigger a b -> (Doc,Doc)
ppTrg p tm = ("pattern",ppTerm p tm)

ppQid :: QID -> (Doc,Doc)
ppQid qid = ("qid",text qid)

ppTmId :: PP a b -> Term a b -> (Doc,Doc)
ppTmId p tm = ("qid",piped (ppTerm p tm))

zmap :: MonadPlus m => (a -> b) -> Maybe a -> m b
zmap f (Just x) = return (f x)
zmap _ Nothing  = mzero

ppQList :: PP a b -> [(b,Type a b)] -> Doc
ppQList p qs = parens (sep [ parens (pp_var p v <+> ppType p t) | (v,t) <- qs ])

ppQ :: Q -> Doc
ppQ q = case q of
    Forall -> "forall"
    Exists -> "exists"

ppFOp :: FOp -> Doc
ppFOp op = case op of
    And     -> "and"
    Or      -> "or"
    Implies -> "=>"
    Equiv   -> "="

ppTOp :: TOp -> Doc
ppTOp op = case op of
    Equal   -> "="
    Unequal -> "distinct"

ppTerm :: PP a b -> Term a b -> Doc
ppTerm p = go
  where
    go tm0 = case tm0 of
        Apply f _ts [] -> pp_symb p f
        Apply f _ts as -> parens (pp_symb p f $\ sep (map go as))
        Var v          -> pp_var p v
        Lit x          -> integer x

