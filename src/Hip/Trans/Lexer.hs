{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Hip.Trans.Lexer where

import Prelude hiding (lex)
import Data.Data
import Data.Char
import Data.Parser.Grempa.Static
import Language.Haskell.TH.Lift

data Tok = LPar | RPar
         | LBrace | RBrace
         | Eq | Arrow | Semi | Under | Bar | DoubleColon
         | Case | Of | Data
         | UIdent { fromTok :: String }
         | LIdent { fromTok :: String }
         | Number { getNum  :: Int    }
  deriving (Show,Eq,Ord,Typeable,Data)

$(deriveLift ''Tok)

lident,uident :: Tok
lident = LIdent ""
uident = UIdent ""

number :: Tok
number = Number 0

instance ToPat Tok where toPat = toConstrPat

lex :: String -> [Tok]
lex []           = []
lex ('(':xs)     = LPar   : lex xs
lex (')':xs)     = RPar   : lex xs
lex ('{':xs)     = LBrace : lex xs
lex ('}':xs)     = RBrace : lex xs
lex ('=':xs)     = Eq     : lex xs
lex ('-':'>':xs) = Arrow  : lex xs
lex (';':xs)     = Semi   : lex xs
lex ('_':xs)     = Under  : lex xs
lex ('|':xs)     = Bar    : lex xs
lex (':':':':xs) = DoubleColon  : lex xs
lex ('c':'a':'s':'e':xs) = Case : lex xs
lex ('o':'f':xs)         = Of   : lex xs
lex ('d':'a':'t':'a':xs) = Data : lex xs
lex s@(x:xs)
    | isLower x = lexIdent LIdent s
    | isUpper x = lexIdent UIdent s
    | isSpace x = lex xs
    | isDigit x = case reads s of
                     [(n,s')] -> Number n : lex s'
                     _        -> error "lex failed to read after number"
    | otherwise = error $ "lex failed on unknow character " ++ [x]

lexIdent :: (String -> Tok) -> String -> [Tok]
lexIdent c s = let (i,s') = span isAlphaNum s
               in  c i : lex s'
