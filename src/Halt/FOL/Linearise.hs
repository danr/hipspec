-- Linearises into TPTP
{-# LANGUAGE PatternGuards #-}
module Halt.FOL.Linearise where

import Outputable

import Data.List

import Halt.Util
import Halt.PrimCon
import Halt.FOL.Internals.Internals
import Halt.FOL.Abstract

data Style q v = Style { linFun   :: v -> SDoc
                       -- ^ Pretty printing functions and variables
                       , linCtor   :: v -> SDoc
                       -- ^ Pretty printing constructors
                       , linQVar  :: q -> SDoc
                       -- ^ Quantified variables
                       , linApp   :: SDoc
                       -- ^ The app/@ symbol
                       , linMin   :: SDoc
                       -- ^ The min symbol
                       , linCF    :: SDoc
                       -- ^ The CF symbol
                       , linProj  :: Int -> v -> SDoc
                       -- ^ Projections
                       , linPtr   :: v -> SDoc
                       -- ^ Pointers
                       , linConstant :: PrimCon -> SDoc
                       -- ^ Constants
                       , linCNF   :: Bool
                       -- ^ Write things in cnf if possible
                       , linComments :: Bool
                       -- ^ Print comments
                       }

-- | Linearise a term
--   The way to carry out most of the work is determined in the Style.
linTm :: Style q v -> Term q v -> SDoc
linTm st tm = case tm of
    Fun a []    -> linFun st a
    Fun a tms   -> linFun st a <> parens (csv (map (linTm st) tms))
    Ctor a []   -> linCtor st a
    Ctor a tms  -> linCtor st a <> parens (csv (map (linTm st) tms))
    App t1 t2   -> linApp st <> parens (csv (map (linTm st) [t1,t2]))
    Proj i c t  -> linProj st i c <> parens (linTm st t)
    Ptr a       -> linPtr st a
    QVar a      -> linQVar st a
    Constant c  -> linConstant st c

linEqOp :: Style q v -> SDoc -> Term q v -> Term q v -> SDoc
linEqOp st op t1 t2 = linTm st t1 <+> op <+> linTm st t2

linBinOp :: Style q v -> SDoc -> [Formula q v] -> SDoc
linBinOp st op fs = cat (punctuate (fluff op) (map (linForm st parens) fs))

linQuant :: Style q v -> SDoc -> [q] -> Formula q v -> SDoc
linQuant st op qs f = hang (op <+> brackets (csv (map (linQVar st) qs)) <+> colon)
                           4
                           (linForm st parens f)

linForm :: Style q v -> (SDoc -> SDoc) -> Formula q v -> SDoc
linForm st par form = case form of
    Equal   t1 t2 -> linEqOp st equals t1 t2
    Unequal t1 t2 -> linEqOp st unequals t1 t2
    And fs        -> par (linBinOp st ampersand fs)
    Or  fs        -> par (linBinOp st pipe fs)
    Implies f1 f2 -> par (linBinOp st darrow [f1,f2])
    Neg f         -> (not (isLiteral f) ? par) (tilde <> linForm st parens f)
    Forall qs f   -> par (linQuant st bang qs f)
    Exists qs f   -> par (linQuant st questmark qs f)
    Min tm        -> linMin st <> parens (linTm st tm)
    CF tm         -> linCF st <> parens (linTm st tm)

linClause :: Style q v -> Clause q v -> SDoc
linClause st (Comment s)
    | linComments st = text ("\n" ++ intercalate "\n" (map ("% " ++) (lines s)))
    | otherwise      = empty
linClause st (Clause cl_name cl_type cl_formula)
    | linCNF st, Just lits <- simpleCNF (((cl_type == Conjecture) ? neg) cl_formula)
       = linClEntry (text "cnf") cl_name cl_type (linBinOp st pipe lits)
    | otherwise
       = linClEntry (text "fof") cl_name cl_type (linForm st id cl_formula)

linClType :: ClType -> SDoc
linClType ty = case ty of
    Axiom             -> text "axiom"
    Lemma             -> text "lemma"
    Hypothesis        -> text "hypothesis"
    Definition        -> text "definition"
    Conjecture        -> text "conjecture"
    NegatedConjecture -> text "negated_conjecture"
    Question          -> text "question"

linClEntry :: SDoc -> String -> ClType -> SDoc -> SDoc
linClEntry fof cl_name cl_type content =
    hang (hcat [fof,lparen,text (prettyName cl_name),comma,space,linClType cl_type,comma])
         4 (content <> rparen <> dot)

linClauses :: Style q v -> [Clause q v] -> SDoc
linClauses st cls = vcat (map (linClause st) cls)

linTPTP :: Style q v -> [Clause q v] -> String
linTPTP st = showSDoc . linClauses st

-- TPTP escaping utilites, unused for now
lowercase :: Char -> Bool
lowercase n = 'a' <= n && n <= 'z'

lowerNumeric :: Char -> Bool
lowerNumeric n = lowercase n || '0' <= n && n <= '9' || n == '_'

escape' :: String -> String
escape' = map escapeChar'
  where escapeChar' '\'' = '_'
        escapeChar' x    = x

prettyName :: String -> String
prettyName name = case escape' name of
  ns | all lowerNumeric ns -> ns
     | otherwise           -> "'" ++ ns ++ "'"

-- Utilities

fluff :: SDoc -> SDoc
fluff d = space <> d <> space

csv :: [SDoc] -> SDoc
csv = cat . punctuate comma

unequals :: SDoc
unequals = text "!="

ampersand :: SDoc
ampersand = char '&'

pipe :: SDoc
pipe = char '|'

tilde :: SDoc
tilde = char '~'

bang :: SDoc
bang = char '!'

questmark :: SDoc
questmark = char '?'

