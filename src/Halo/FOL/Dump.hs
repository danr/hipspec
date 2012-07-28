-- A more brutal way of dumping the clauses to TPTP rather than
-- pretty-printing them.
{-# LANGUAGE RecordWildCards, PatternGuards #-}
module Halo.FOL.Dump ( dumpTPTP ) where

import Var

import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract

import qualified Data.DList as DL

type DLDoc = DL.DList Char

-- | Dump a set of clauses to a String
dumpTPTP :: [Clause'] -> String
dumpTPTP = DL.toList . dumpClauses

-- | DUmp a set of clauses
dumpClauses :: [Clause'] -> DLDoc
dumpClauses cls = cat (map dumpClause cls)

-- | Dumps a clause
--   This function also transforms formulae to CNF, which might indeed
--   be a little strange to do here
dumpClause :: Clause' -> DLDoc
dumpClause (Clause _cl_name cl_type cl_formula) = case simpleCNF cl_formula' of
    Just atoms -> dumpClEntry (text "cnf") cl_type' (dumpBinOp pipe atoms)
    _          -> dumpClEntry (text "fof") cl_type (dumpForm id cl_formula)
  where
    (cl_type',cl_formula')
        = (cl_type == Conjecture ? const NegatedConjecture *** neg)
        $ (cl_type,cl_formula)
dumpClause _ = empty

-- | Dump a clause entry fof/cnf, and its formula
dumpClEntry :: DLDoc -> ClType -> DLDoc -> DLDoc
dumpClEntry fof cl_type content =
    fof <>
    parens (char 'x' <> comma <> dumpClType cl_type <> comma <> content)
    <> dot <> newline

-- | Dump the type of the clause
dumpClType :: ClType -> DLDoc
dumpClType ty = case ty of
    Conjecture -> text "conjecture"
    _          -> text "axiom"

-- | Dump a formula.
--   Second argument is if it should be enclosed in parentheses.
dumpForm :: (DLDoc -> DLDoc) -> Formula' -> DLDoc
dumpForm par form = case form of
    Equal   t1 t2 -> dumpEqOp equals t1 t2
    Unequal t1 t2 -> dumpEqOp unequals t1 t2
    And fs        -> par (dumpBinOp ampersand fs)
    Or  fs        -> par (dumpBinOp pipe fs)
    Implies f1 f2 -> par (dumpBinOp darrow [f1,f2])
    Neg f         -> (not (isAtomic f) ? par) (space <> tilde <> dumpForm parens f)
    Forall qs f   -> par (dumpQuant bang qs f)
    Exists qs f   -> par (dumpQuant questmark qs f)
    Min tm        -> text "$min" <> parens (dumpTm tm)
    MinRec tm     -> text "minrec" <> parens (dumpTm tm)
    CF tm         -> text "cf" <> parens (dumpTm tm)

-- | Dump the equality operations: ==, !=
dumpEqOp :: DLDoc -> Term' -> Term' -> DLDoc
dumpEqOp op t1 t2 = dumpTm t1 <> op <> dumpTm t2

-- | Dump binary operations: &, |, =>
dumpBinOp :: DLDoc -> [Formula'] -> DLDoc
dumpBinOp op fs = cat (punctuate op (map (dumpForm parens) fs))

-- | Dump quantifiers: ! [..] :, ? [..] :
--   op list should _not_ be empty
dumpQuant ::  DLDoc -> [Var] -> Formula' -> DLDoc
dumpQuant op qs f =
    op <> brackets (csv (map dumpQVar qs)) <> colon <> dumpForm parens f

dumpQVar :: Var -> DLDoc
dumpQVar = (char 'Q' <>) . dumpVar

-- | Dump a term
dumpTm :: Term' -> DLDoc
dumpTm tm = case tm of
    Fun  a tms  -> char 'f' <> dumpVar a <> dumpArgs tms
    Ctor a tms  -> char 'c' <> dumpVar a <> dumpArgs tms
    Skolem a    -> char 'k' <> dumpVar a
    App t1 t2   -> char 'a' <> dumpArgs [t1,t2]
    Proj i c t  -> char 's' <> (text . show) i <> dumpVar c <> dumpArgs [t]
    Ptr a       -> char 'p' <> dumpVar a
    QVar a      -> dumpQVar a

dumpVar :: Var -> DLDoc
dumpVar = text . show . varUnique

dumpArgs :: [Term'] -> DLDoc
dumpArgs [] = empty
dumpArgs xs = parens (csv (map dumpTm xs))

-- Utilities

cat :: [DLDoc] -> DLDoc
cat = DL.concat

char :: Char -> DLDoc
char = DL.singleton

text :: String -> DLDoc
text = DL.fromList

(<>) :: DLDoc -> DLDoc -> DLDoc
(<>) = DL.append

punctuate :: DLDoc -> [DLDoc] -> [DLDoc]
punctuate _ []     = []
punctuate p (x:xs) = go x xs
  where
    go d []     = [d]
    go d (e:es) = (d <> p) : go e es

csv :: [DLDoc] -> DLDoc
csv = cat . punctuate comma

newline :: DLDoc
newline = char '\n'

equals :: DLDoc
equals = char '='

unequals :: DLDoc
unequals = text "!="

ampersand :: DLDoc
ampersand = char '&'

pipe :: DLDoc
pipe = char '|'

tilde :: DLDoc
tilde = char '~'

bang :: DLDoc
bang = char '!'

questmark :: DLDoc
questmark = char '?'

colon :: DLDoc
colon = char ':'

comma :: DLDoc
comma = char ','

dot :: DLDoc
dot = char '.'

space :: DLDoc
space = char ' '

darrow :: DLDoc
darrow = text "=>"

empty :: DLDoc
empty = DL.empty

parens :: DLDoc -> DLDoc
parens x = '(' `DL.cons` (x `DL.snoc` ')')

brackets :: DLDoc -> DLDoc
brackets x = '[' `DL.cons` (x `DL.snoc` ']')
