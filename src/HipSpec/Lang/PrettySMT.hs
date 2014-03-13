{-# LANGUAGE OverloadedStrings,PatternGuards #-}
module HipSpec.Lang.PrettySMT where

import Text.PrettyPrint

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.PrettyUtils

ppClause :: PP a b -> Clause a b -> Doc
ppClause p cls = case cls of
    SortSig x _n            -> parens ("declare-sort" $\ pp_symb p x)
    TypeSig x _tvs args res -> parens ("declare-fun" $\ sep
                                        [pp_symb p x
                                        ,parens (sep (map (ppType p) args))
                                        ,ppType p res])
    Clause _ _ cl _tvs fm   -> parens ("assert" $\
                                        ppForm p
                                            (case cl of {Goal -> neg; _ -> id} $ fm))
    Comment s               -> vcat (map (\ l -> ";" <+> text l) (lines s))

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
      | Just (q,(bs,f)) <- collectQ f0 -> parens (ppQ q $\ sep [ppQList p bs,ppForm p f])
    TOp top t1 t2 -> parens (ppTOp top $\ sep (map (ppTerm p) [t1,t2]))
    Neg f         -> parens ("not" $\ ppForm p f)
--    Pred q fs     -> p q <> csv (map (ppForm p) fs)
    FOp{} -> error "PrettySMT.ppForm FOp"
    Q{}   -> error "PrettySMT.ppForm Q"

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

{-

linPrim :: Prim -> SDoc
linPrim p = case p of
    Add -> char '+'
    Sub -> char '-'
    Mul -> char '*'
    Eq  -> char '='
    Ne  -> text "!=" -- will this work?
    Lt  -> char '<'
    Le  -> text "<="
    Ge  -> text ">="
    Gt  -> char '>'
    LiftBool -> linLiftBool

linLiftBool :: SDoc
linLiftBool = text "lift_bool"

linLiftBoolDefn :: SDoc
linLiftBoolDefn = vcat $
    linDeclFun linLiftBool [linBool] linDomain :
    [ parens $ text "assert" <+>
        parens (equals <+> parens (linLiftBool <+> text in_bool)
                       <+> in_domain)
    | (in_bool,in_domain) <-
        [("true",linCtor (dataConWorkId trueDataCon))
        ,("false",linCtor (dataConWorkId falseDataCon))
        ]
    ]

primType :: Prim -> ([SDoc],SDoc)
primType p = case p of
    Add      -> int_int_int
    Sub      -> int_int_int
    Mul      -> int_int_int
    Eq       -> int_int_bool
    Ne       -> int_int_bool
    Lt       -> int_int_bool
    Le       -> int_int_bool
    Ge       -> int_int_bool
    Gt       -> int_int_bool
    LiftBool -> ([linBool],linDomain)
  where
    int_int_int  = ([linInt,linInt],linInt)
    int_int_bool = ([linInt,linInt],linBool)
 -}
