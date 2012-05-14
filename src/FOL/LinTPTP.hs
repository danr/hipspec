-- Linearises into TPTP
{-# LANGUAGE FlexibleInstances #-}
module FOL.LinTPTP where

import Outputable
import Var
import Id
import Name

import Halt.Common

import FOL.Abstract

import Data.Char

data Style a = Style { linVar   :: a -> SDoc
                     -- ^ Pretty printing variables
                     , linQVar :: a -> SDoc
                     -- ^ Quantified variables
                     , linApp   :: SDoc
                     -- ^ The app/@ symbol
                     , linMin   :: SDoc
                     -- ^ The min symbol
                     , linCF    :: SDoc
                     -- ^ The CF symbol
                     , linProj  :: Int -> a -> SDoc
                     -- ^ Projections
                     , linPtr   :: a -> SDoc
                     -- ^ Pointers
                     , linCNF   :: Bool
                     -- ^ Write things in cnf if possible
                     , linComments :: Bool
                     -- ^ Print comments
                     }

stringStyle :: Style String
stringStyle = Style
    { linVar  = text . prettyName
    , linQVar = text
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i n -> text (n ++ "_" ++ show i)
    , linPtr  = text . (++ ".ptr")
    , linCNF  = True
    , linComments = True
    }

lazyStyle :: Style Var
lazyStyle = Style
    { linVar  = text . prettyName . lower . showSDoc . ppr . maybeLocaliseName . idName
    , linQVar = text . capInit . showSDoc . ppr . maybeLocaliseName . idName
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i -> text . prettyName . (++  "_" ++ show i) . lower . showSDoc . ppr . localiseName . idName
    , linPtr  = text . prettyName . (++ ".ptr") . showSDoc . ppr
    , linCNF  = True
    , linComments = True
    }
  where
    maybeLocaliseName n | isSystemName n = n
                        | otherwise      = localiseName n

    capInit (x:xs) | isAlpha x = toUpper x : xs
                   | otherwise = 'Q':x:xs
    capInit "" = "Q"

    lower = map toLower


-- | Linearise a term
--   The way to carry out most of the work is determined in the Style.
linTm :: Style a -> Term a -> SDoc
linTm st tm = case tm of
    Fun a []    -> linVar st a
    Fun a tms   -> linVar st a <> parens (csv (map (linTm st) tms))
    App t1 t2   -> linApp st <> parens (csv (map (linTm st) [t1,t2]))
    Proj i c t  -> linProj st i c <> parens (linTm st t)
    Ptr a       -> linPtr st a
    QVar a      -> linQVar st a

linEqOp :: Style a -> SDoc -> Term a -> Term a -> SDoc
linEqOp st op t1 t2 = linTm st t1 <+> op <+> linTm st t2

linBinOp :: Style a -> SDoc -> [Formula a] -> SDoc
linBinOp st op fs = cat (punctuate (fluff op) (map (linForm st parens) fs))

linQuant :: Style a -> SDoc -> [a] -> Formula a -> SDoc
linQuant st op qs f = hang (op <+> brackets (csv (map (linQVar st) qs)) <+> colon)
                           4
                           (linForm st parens f)

linForm :: Style a -> (SDoc -> SDoc) -> Formula a -> SDoc
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

linClause :: Style a -> Clause a -> SDoc
linClause st (Comment s)
    | linComments st = text s
    | otherwise      = empty
linClause st (Clause cl_type cl_name cl_formula)
    | linCNF st, Just lits <- simpleCNF cl_formula
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

linClauses :: Style a -> [Clause a] -> SDoc
linClauses st cls = vcat (map (linClause st) cls)

outputTPTP :: [Clause Var] -> IO ()
outputTPTP = putStrLn . showSDoc . linClauses lazyStyle

writeTPTP :: FilePath -> [Clause Var] -> IO ()
writeTPTP file = writeFile file . (++ "\n") . showSDoc . linClauses lazyStyle

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

