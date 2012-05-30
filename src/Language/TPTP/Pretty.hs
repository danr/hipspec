{-# LANGUAGE FlexibleInstances, TemplateHaskell
 #-}
module Language.TPTP.Pretty (prettyTPTP,outputTPTP,writeTPTP) where

import Language.TPTP
import Data.List

class PrettyTPTP p where
    prettyTPTP :: p -> String

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
  n:ns | lowercase n && all lowerNumeric ns -> n:ns
  ns                                        -> "'" ++ ns ++ "'"

instance PrettyTPTP FunName where
    prettyTPTP = prettyName . funName

instance PrettyTPTP RelName where
    prettyTPTP = prettyName . relName

instance PrettyTPTP VarName where
    prettyTPTP = map escapeVarChar . show
      where
        escapeVarChar '.'  = '_'
        escapeVarChar '\'' = '_'
        escapeVarChar x    = x

p :: PrettyTPTP a => a -> String
p = prettyTPTP

csv :: PrettyTPTP a => [a] -> String
csv = intercalate "," . map p

argList :: PrettyTPTP a => [a] -> String
argList [] = ""
argList xs = paren (csv xs)

bindList :: PrettyTPTP a => [a] -> String
bindList [] = error "Empty bind list"
bindList xs = "[" ++ csv xs ++ "]"

paren :: String -> String
paren s = "(" ++ s ++ ")"

instance PrettyTPTP Term where
    prettyTPTP (Fun f args) = p f ++ argList args
    prettyTPTP (Var x)      = p x

instance PrettyTPTP BinOp where
    prettyTPTP (:&)   = " & "
    prettyTPTP (:|)   = " \n\t| "
    prettyTPTP (:=>)  = " => "
    prettyTPTP (:<=>) = " <=> "

instance PrettyTPTP Formula where
    prettyTPTP (EqOp t1 (:==) t2) = p t1 ++ " = "  ++ p t2
    prettyTPTP (EqOp t1 (:!=) t2) = p t1 ++ " != " ++ p t2
    prettyTPTP (Rel r args)       = p r ++ argList args
    prettyTPTP (Neg f)            = "~ " ++ paren (p f)
    prettyTPTP (BinOp f1 op f2)   = paren (p f1) ++ p op ++ paren (p f2)
    prettyTPTP (Forall vs f)      = "! " ++ bindList vs ++ ": " ++ paren (p f)
    prettyTPTP (Exists vs f)      = "? " ++ bindList vs ++ ": " ++ paren (p f)

pdecl :: String -> String -> Formula -> String
pdecl n t f = "fof" ++ paren (n ++ "," ++ t ++ "," ++ prettyTPTP f) ++ "."

declType :: Decl -> String
declType Axiom{}      = "axiom"
declType Conjecture{} = "conjecture"
declType Question{}   = "question"
declType NegConj{}    = "negated_conjecture"
declType Lemma{}      = "lemma"
declType Hypothesis{} = "hypothesis"
declType Definition{} = "definition"

instance PrettyTPTP Decl where
    prettyTPTP d = pdecl (prettyName (declName d)) (declType d) (declFormula d)

instance PrettyTPTP [Decl] where
    prettyTPTP ds = unlines (map prettyTPTP ds)

writeTPTP :: PrettyTPTP a => FilePath -> a -> IO ()
writeTPTP file a = writeFile file (prettyTPTP a)

outputTPTP :: PrettyTPTP a => a -> IO ()
outputTPTP = putStr . prettyTPTP
