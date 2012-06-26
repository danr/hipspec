-- Linearises (pretty prints) our FOL representation into TPTP
{-# LANGUAGE PatternGuards #-}
module Halo.FOL.Linearise where

import Outputable

import Data.List

import Halo.Util
import Halo.PrimCon
import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract
import Halo.FOL.Style

-- | Linearise a set of clauses to a String
linTPTP :: Style q v -> [Clause q v] -> String
linTPTP st = (++ "\n") . showSDoc . linClauses st

-- | Linearise a set of clauses
linClauses :: Style q v -> [Clause q v] -> SDoc
linClauses st cls = vcat (map (linClause st) cls)

-- | Linearises a clause
--   This function also transforms formulae to CNF, which might indeed
--   be a little strange to do in the lineariser.
linClause :: Style q v -> Clause q v -> SDoc
linClause st (Comment s)
    | linComments st = text ("\n" ++ intercalate "\n" (map ("% " ++) (lines s)))
    | otherwise      = empty
linClause st (Clause cl_name cl_type cl_formula)
    | linCNF st
    , let (cl_type',cl_formula')
              = (cl_type == Conjecture ? const NegatedConjecture *** neg)
              $ (cl_type,cl_formula)
    , Just lits <- simpleCNF cl_formula'
        = linClEntry (text "cnf") cl_name cl_type' (linBinOp st pipe lits)
    | otherwise
        = linClEntry (text "fof") cl_name cl_type (linForm st id cl_formula)

-- | Linearise a clause entry fof/cnf, plus axiom name, and its formula
linClEntry :: SDoc -> String -> ClType -> SDoc -> SDoc
linClEntry fof cl_name cl_type content =
    hang (hcat [fof,lparen,text (escape cl_name)
               ,comma,space,linClType cl_type,comma])
         4 (content <> rparen <> dot)

-- | Linearise the type of the clause
linClType :: ClType -> SDoc
linClType ty = case ty of
    Axiom             -> text "axiom"
    Lemma             -> text "lemma"
    Hypothesis        -> text "hypothesis"
    Definition        -> text "definition"
    Conjecture        -> text "conjecture"
    NegatedConjecture -> text "axiom"
                      -- ^ SPASS ignores fof negated_conjecture,
                      --   so we write these as axiom instead
    Question          -> text "question"

-- | Linearise a formula.
--   Second argument is if it should be enclosed in parentheses.
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

-- | Linearise the equality operations: ==, !=
linEqOp :: Style q v -> SDoc -> Term q v -> Term q v -> SDoc
linEqOp st op t1 t2 = linTm st t1 <+> op <+> linTm st t2

-- | Linearise binary operations: &, |, =>
linBinOp :: Style q v -> SDoc -> [Formula q v] -> SDoc
linBinOp st op fs = cat (punctuate (fluff op) (map (linForm st parens) fs))

-- | Linearise quantifiers: ! [..] :, ? [..] :
--   op list should _not_ be empty
linQuant :: Style q v -> SDoc -> [q] -> Formula q v -> SDoc
linQuant st op qs f = hang
    (op <+> brackets (csv (map (linQVar st) qs)) <+> colon) 4
    (linForm st parens f)

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

-- | Encloses a string in 'single quotes' if it is not a valid tptp
--   identifier without it.
escape :: String -> String
escape s = case escape' s of
    s' | all lowerNumeric s' -> s'
       | otherwise           -> "'" ++ s' ++ "'"
  where
    -- Replace all ' to _
    escape' :: String -> String
    escape' = map escapeChar

    -- Replace a ' to _
    escapeChar '\'' = '_'
    escapeChar x    = x

-- | Char is lowercase
lowercase :: Char -> Bool
lowercase n = 'a' <= n && n <= 'z'

-- | Char is lowercase or numeric or _
lowerNumeric :: Char -> Bool
lowerNumeric n = lowercase n || '0' <= n && n <= '9' || n == '_'

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

