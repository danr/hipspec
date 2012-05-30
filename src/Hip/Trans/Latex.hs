{-# LANGUAGE ViewPatterns #-}
-- This module is only to be used for TPTP produced by the HFOL.Trans->TPTP tool
module Hip.Trans.Latex where

import Language.TPTP
import Hip.Util (isOp)

import qualified Hip.Trans.Core as C
import Hip.Trans.Pretty

import Hip.Trans.Constructors

import Control.Monad.State
import Control.Applicative

import Data.List
import Data.Char

runLatex :: Latex a => a -> String
runLatex = (++ "\\\\") .  (`evalState` False) . latex

escape :: String -> String
escape = fixUnderscore . concatMap e
 where e '&' = "\\&"
       e c   = [c]

       fixUnderscore s =
           case break (== '_') s of
                    (l,'_':rest) -> l ++ '_':'{':fixUnderscore rest ++ "}"
                    _            -> s

latexHeader :: String -> [Decl] -> String
latexHeader file fs = unlines $
  ["\\documentclass{article}"
  ,"\\usepackage[a4paper]{geometry}"
  ,"\\usepackage{amsmath}"
  ,"\\allowdisplaybreaks"
  ,"\\begin{document}"
  ,"\\title{" ++ file ++ "}"
  ,"\\maketitle"
  ,"\\section{Datatypes and pointers}"
  ,"\\begin{align*}"
  ]
  ++ map runLatex fs ++
  ["\\end{align*}"
  ,"\\newpage"
  ]

latexDecl :: C.Decl -> [Decl] -> String
latexDecl C.Data{}          _  = error "latexDecl on data"
latexDecl d@(C.Func fn _ _) fs
  | null fs = ""
  | otherwise = unlines $
  ["\\section{$" ++ escape fn ++ "$}"
  ,""
  ,"\\subsection{Definition}"
  ,""
  ,"\\begin{verbatim}"
  ,prettyCore d
  ,"\\end{verbatim}"
  ,""
  ,"\\subsection{Axioms}"
  ,""
  ,"\\begin{align*}"
  ]
  ++ map runLatex fs ++
  ["\\end{align*}"
  ,"\\newpage"
  ]

latexFooter :: String
latexFooter = "\\end{document}"

class Latex a where
  latex :: a -> State Bool String

instance Latex Decl where
  latex (declFormula -> phi) = latex phi

quantifier :: Bool -> [VarName] -> Formula -> State Bool String
quantifier fa xs phi = do
  phi' <- latex phi
  return $ (if fa then " \\forall \\, " else " \\exists \\, ")
         ++ intercalate " \\, " (map (map toLower . varName) xs)
         ++ " \\, . \\, " ++ phi'

eqop :: EqOp -> String
eqop (:==) = " = "
eqop (:!=) = " \\neq "

instance Latex EqOp where
  latex op = do
    b <- get
    put True
    if b then return (eqop op)
         else return (" & " ++ eqop op)

instance Latex BinOp where
  latex (:&) = return " \\wedge "
  latex (:|) = put True >> return "\\\\\n & \\vee "
  latex (:=>) = return " \\rightarrow "
  latex (:<=>) = return " \\leftrightarrow "


paren :: BinOp -> String -> String
paren (:=>) s = "(" ++ s ++ ")"
paren (:&)  s = "(" ++ s ++ ")"
paren _     s = s

-- | append for three arguments
trippend :: [a] -> [a] -> [a] -> [a]
trippend x y z = x ++ y ++ z

instance Latex Formula where
  latex (Forall xs phi) = quantifier True xs phi
  latex (Exists xs phi) = quantifier False xs phi
  latex (EqOp f1 op f2) = liftM3 trippend
                                 (latex f1)
                                 (latex op)
                                 (latex f2)
  latex (BinOp f1 (:=>) f2) = paren (:=>) <$> liftM3 trippend
                                                  (latex f2)
                                                  (return " \\leftarrow ")
                                                  (latex f1)
  latex (BinOp f1 op f2) = paren op <$> liftM3 trippend
                                               (latex f1)
                                               (latex op)
                                               (latex f2)
  latex (Neg f) = ("\\not" ++) <$> latex f
  latex (Rel r []) = return $ relName r
  latex (Rel r as) = do
    as' <- mapM latex as
    return (relName r ++ "(" ++ intercalate "," as' ++ ")")

showFunName :: FunName -> String
showFunName (FunName f) | f == bottomName = "\\bot"
                        | otherwise       = escape f

parenTerm :: Term -> String -> String
parenTerm (Fun _ (_:_)) s = "(" ++ s ++ ")"
parenTerm _             s = s

instance Latex Term where
  latex (Var x)    = return $ map toLower (escape (varName x))
  latex (Fun f []) = return $ "\\mathrm{" ++ showFunName f ++ "}"
  latex (Fun op [x,y]) | isOp (funName op) = do
    x' <- parenTerm x <$> latex x
    y' <- parenTerm y <$> latex y
    return (x' ++ " \\, " ++ showFunName op ++ " \\, " ++ y')
  latex (Fun f as) = do
    as' <- mapM latex as
    return ("\\mathrm{" ++ showFunName f ++ "}"
            ++ "(" ++ intercalate "," as' ++ ")")