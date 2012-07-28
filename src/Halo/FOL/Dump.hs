-- A more brutal way of dumping the clauses to TPTP rather than
-- pretty-printing them.
{-# LANGUAGE RecordWildCards, PatternGuards #-}
module Halo.FOL.Dump ( dumpTPTP ) where

import Outputable hiding (quote)
import Var

import Halo.Util
import Halo.FOL.Internals.Internals
import Halo.FOL.Abstract

-- | Dump a set of clauses to a String
dumpTPTP :: [Clause'] -> String
dumpTPTP = (++ "\n") . showSDoc . dumpClauses

-- | DUmp a set of clauses
dumpClauses :: [Clause'] -> SDoc
dumpClauses cls = vcat (map dumpClause cls)

-- | Dumps a clause
--   This function also transforms formulae to CNF, which might indeed
--   be a little strange to do here
dumpClause :: Clause' -> SDoc
dumpClause (Clause _cl_name cl_type cl_formula) = case simpleCNF cl_formula' of
    Just atoms -> dumpClEntry (text "cnf") cl_type' (dumpBinOp pipe atoms)
    _          -> dumpClEntry (text "fof") cl_type (dumpForm id cl_formula)
  where
    (cl_type',cl_formula')
        = (cl_type == Conjecture ? const NegatedConjecture *** neg)
        $ (cl_type,cl_formula)
dumpClause _ = empty

-- | Dump a clause entry fof/cnf, and its formula
dumpClEntry :: SDoc -> ClType -> SDoc -> SDoc
dumpClEntry fof cl_type content =
    fof <>
    parens (char 'x' <> comma <> dumpClType cl_type <> comma <> content)
    <> dot

-- | Dump the type of the clause
dumpClType :: ClType -> SDoc
dumpClType ty = case ty of
    Conjecture -> text "conjecture"
    _          -> text "axiom"

-- | Dump a formula.
--   Second argument is if it should be enclosed in parentheses.
dumpForm :: (SDoc -> SDoc) -> Formula' -> SDoc
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
dumpEqOp :: SDoc -> Term' -> Term' -> SDoc
dumpEqOp op t1 t2 = dumpTm t1 <> op <> dumpTm t2

-- | Dump binary operations: &, |, =>
dumpBinOp :: SDoc -> [Formula'] -> SDoc
dumpBinOp op fs = hcat (punctuate op (map (dumpForm parens) fs))

-- | Dump quantifiers: ! [..] :, ? [..] :
--   op list should _not_ be empty
dumpQuant ::  SDoc -> [Var] -> Formula' -> SDoc
dumpQuant op qs f =
    op <> brackets (csv (map dumpQVar qs)) <> colon <> dumpForm parens f

dumpQVar :: Var -> SDoc
dumpQVar = (char 'Q' <>) . dumpVar

-- | Dump a term
dumpTm :: Term' -> SDoc
dumpTm tm = case tm of
    Fun  a tms  -> char 'f' <> dumpVar a <> dumpArgs tms
    Ctor a tms  -> char 'c' <> dumpVar a <> dumpArgs tms
    Skolem a    -> char 'k' <> dumpVar a
    App t1 t2   -> char 'a' <> dumpArgs [t1,t2]
    Proj i c t  -> char 's' <> ppr i <> dumpVar c <> dumpArgs [t]
    Ptr a       -> char 'p' <> dumpVar a
    QVar a      -> dumpQVar a

dumpVar :: Var -> SDoc
dumpVar = ppr . varUnique

dumpArgs :: [Term'] -> SDoc
dumpArgs [] = empty
dumpArgs xs = parens (csv (map dumpTm xs))

-- Utilities

csv :: [SDoc] -> SDoc
csv = hcat . punctuate comma

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
