{-# LANGUAGE FlexibleInstances #-}
module FOL.Pretty (prettyTPTP,outputTPTP,writeTPTP) where

import FOL.Syn

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
  ns | all lowerNumeric ns -> ns
     | otherwise           -> "'" ++ ns ++ "'"

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
    prettyTPTP (FVar x)     = p x

instance PrettyTPTP BinOp where
    prettyTPTP (:&)   = " & "
    prettyTPTP (:|)   = " | "
    prettyTPTP (:=>)  = " => "
    prettyTPTP (:<=>) = " <=> "

collectBinOp :: BinOp -> Formula -> [Formula]
collectBinOp b f@(BinOp f1 b' f2)
    | b == b'   = collectBinOp b f1 ++ collectBinOp b f2
    | otherwise = [f]
collectBinOp _ f = [f]

instance PrettyTPTP Formula where
    prettyTPTP = pForm 0

pForm :: Int -> Formula -> String
pForm i f = case f of
    EqOp t1 (:==) t2 -> p t1 ++ " = "  ++ p t2
    EqOp t1 (:!=) t2 -> p t1 ++ " != " ++ p t2
    Rel r args       -> p r ++ argList args
    Neg f'           -> enclose (i > 2) $ "~ " ++ pForm 2 f'
    BinOp _ b _      -> enclose (i > 1) $
                             foldr1 (\x y -> x ++ prettyTPTP b ++ y)
                                    (map (pForm 2) (collectBinOp b f))
    Forall vs f'     -> enclose (i > 1) $ "! " ++ bindList vs ++ ": " ++ pForm 3 f'
    Exists vs f'     -> enclose (i > 1) $ "? " ++ bindList vs ++ ": " ++ pForm 3 f'

enclose :: Bool -> String -> String
enclose True  = paren
enclose False = id

pdecl :: String -> String -> Formula -> String
pdecl n t f = "fof" ++ paren (n ++ "," ++ t ++ "," ++ prettyTPTP f) ++ "."

pDeclType :: DeclType -> String
pDeclType CNF{}        = "cnf"
pDeclType Axiom{}      = "axiom"
pDeclType Conjecture{} = "conjecture"
pDeclType Question{}   = "question"
pDeclType NegConj{}    = "negated_conjecture"
pDeclType Lemma{}      = "lemma"
pDeclType Hypothesis{} = "hypothesis"
pDeclType Definition{} = "definition"

instance PrettyTPTP FDecl where
    prettyTPTP (FDecl CNF n f) = "cnf" ++ paren (prettyName n ++ ",axiom," ++ prettyTPTP f) ++ "."
    prettyTPTP d = pdecl (prettyName (declName d)) (pDeclType (declType d)) (declFormula d)

instance PrettyTPTP [FDecl] where
    prettyTPTP ds = unlines (map prettyTPTP ds)

writeTPTP :: PrettyTPTP a => FilePath -> a -> IO ()
writeTPTP file a = writeFile file (prettyTPTP a)

outputTPTP :: PrettyTPTP a => a -> IO ()
outputTPTP = putStr . prettyTPTP
