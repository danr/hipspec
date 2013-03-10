-- Linearises (pretty prints) our FOL representation into TPTP
{-# LANGUAGE RecordWildCards, PatternGuards, EmptyDataDecls #-}
module Halo.FOL.Linearise
    ( linStrStyleTPTP
    , linVarStyleTPTP
    , StyleConf(..)
    ) where

import Outputable hiding (quote)
import Var

import Data.Char
import Data.List

import Halo.Shared
import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract

data StyleConf

linStrStyleTPTP = error "lin tptp"
linVarStyleTPTP = error "lin tptp"

{-
-- | Linearise string clauses with strStyle
linStrStyleTPTP :: StyleConf -> [StrClause] -> String
linStrStyleTPTP = linTPTP . strStyle

-- | Linearise string clauses with strStyle
linVarStyleTPTP :: StyleConf -> [Clause'] -> String
linVarStyleTPTP = linTPTP . varStyle

-- | Linearise a set of clauses to a String
linTPTP :: Style q v -> [Clause q v] -> String
linTPTP st = (++ "\n") . portableShowSDoc . linClauses st

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
    hang (hcat [fof,lparen,text (quoteEscape cl_name)
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
                      -- SPASS ignores fof negated_conjecture,
                      -- so we write these as axiom instead
    Question          -> text "question"

-- | Linearise a formula.
--   Second argument is if it should be enclosed in parentheses.
linForm :: Style q v -> (SDoc -> SDoc) -> Formula q v -> SDoc
linForm st par form = case form of
    Equal   t1 t2    -> linEqOp st equals t1 t2
    Unequal t1 t2    -> linEqOp st unequals t1 t2
    And fs           -> par (linBinOp st ampersand fs)
    Or  fs           -> par (linBinOp st pipe fs)
    Implies f1 f2    -> par (linBinOp st darrow [f1,f2])
    Equiv   f1 f2    -> par (linBinOp st dblarrow [f1,f2])
    Neg f            -> (not (isAtomic f) ? par) (tilde <> linForm st parens f)
    Forall qs f      -> par (linQuant st bang qs f)
    Exists qs f      -> par (linQuant st questmark qs f)
    Total tm         -> linTotal st <> parens (linTm st tm)

-- | Linearise the equality operations: ==, !=
linEqOp :: Style q v -> SDoc -> Term q v -> Term q v -> SDoc
linEqOp st op t1 t2 = linTm st t1 <+> op <+> linTm st t2

-- | Linearise binary operations: &, |, =>
linBinOp :: Style q v -> SDoc -> [Formula q v] -> SDoc
linBinOp st op fs = cat (punctuate' (fluff op) (map (linForm st parens) fs))

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
    Skolem a    -> linSkolem st a
    App t1 t2   -> linApp st <> parens (csv (map (linTm st) [t1,t2]))
    Proj i c t  -> linProj st i c <> parens (linTm st t)
    Ptr a       -> linPtr st a
    QVar a      -> linQVar st a
    Prim p _    -> error $ "linTm: Primitve " ++ show p
    Lit i       -> error $ "linTm: Literal " ++ show i

-- | Encloses a string in 'single quotes' if it is not a valid tptp
--   identifier without it.
quoteEscape :: String -> String
quoteEscape s
    | needsQuote s = quote s
    | otherwise    = s

quoteEscapeQvar :: String -> String
quoteEscapeQvar s
    | not (all isAlphaNumeric s) = quote s
    | otherwise                  = s

quote :: String -> String
quote s = "'" ++ s ++ "'"

-- | Does this need quote?
needsQuote :: String -> Bool
needsQuote (x:xs) = not (isLowerNumeric x && all isAlphaNumeric xs)
needsQuote []     = True

-- | Char is underscore
isUnderscore :: Char -> Bool
isUnderscore c = c == '_'

-- | Char is lowercase or numeric or _
isLowerNumeric :: Char -> Bool
isLowerNumeric c = isLower c || isDigit c || isUnderscore c

-- | Char is alpha or numeric or _
isAlphaNumeric :: Char -> Bool
isAlphaNumeric c = isAlphaNum c || isUnderscore c

-- Utilities

fluff :: SDoc -> SDoc
fluff d = space <> d <> space

csv :: [SDoc] -> SDoc
csv = cat . punctuate' comma

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

punctuate' :: SDoc -> [SDoc] -> [SDoc]
punctuate' _ []     = []
punctuate' p (d:ds) = d : map (p <>) ds


data Style q v = Style
    { linFun      :: v -> SDoc
    -- ^ Pretty printing functions and variables
    , linCtor     :: v -> SDoc
    -- ^ Pretty printing constructors
    , linSkolem   :: v -> SDoc
    -- ^ Pretty printing Skolemised variables
    , linQVar     :: q -> SDoc
    -- ^ Quantified variables
    , linApp      :: SDoc
    -- ^ The app symbol
    , linMin      :: SDoc
    -- ^ The min symbol
    , linMinRec   :: SDoc
    -- ^ The minrec symbol
    , linTotal    :: SDoc
    -- ^ The CF symbol
    , linProj     :: Int -> v -> SDoc
    -- ^ Projections
    , linPtr      :: v -> SDoc
    -- ^ Pointers
    , linCNF      :: Bool
    -- ^ Write things in cnf if possible
    , linComments :: Bool
    -- ^ Print comments
    }

data StyleConf = StyleConf
    { style_cnf        :: Bool
    , style_dollar_min :: Bool
    , style_comments   :: Bool
    }

strStyle :: StyleConf -> Style String String
strStyle StyleConf{..} = Style
    { linFun      = text . quoteEscape . ("f_" ++)
    , linCtor     = text . quoteEscape . ("c_" ++)
    , linSkolem   = text . quoteEscape . ("a_" ++)
    , linQVar     = text . quoteEscapeQvar
    , linApp      = text "app"
    , linMin      = text ((style_dollar_min ? ('$':)) "min")
    , linMinRec   = text "minrec"
    , linCF       = text "cf"
    , linIsType   = text "type"
    , linProj     = \i n -> text (quoteEscape ("p_" ++ show i ++ "_" ++ n))
    , linPtr      = text . quoteEscape . ("ptr_" ++)
    , linCNF      = style_cnf
    , linComments = style_comments
    }

varStyle :: StyleConf -> Style Var Var
varStyle StyleConf{..} = Style
    { linFun      = (char 'f' <>) . ppr . varUnique
    , linCtor     = (char 'c' <>) . ppr . varUnique
    , linSkolem   = (text "sk" <>) . ppr . varUnique
    , linQVar     = (char 'Q' <>) . ppr . varUnique
    , linApp      = text "app"
    , linMin      = text ((style_dollar_min ? ('$':)) "min")
    , linMinRec   = text "minrec"
    , linCF       = text "cf"
    , linIsType   = text "type"
    , linProj     = \i n -> char 's' <> ppr (varUnique n) <> underscore <> ppr i
    , linPtr      = (char 'p' <>) . ppr . varUnique
    , linCNF      = style_cnf
    , linComments = style_comments
    }
     -}
