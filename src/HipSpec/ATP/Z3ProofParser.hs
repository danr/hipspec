{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, PatternGuards, CPP, FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- LICENSE: the s-expr parser in this module is based on lisp-parser on
-- hackage, http://hackage.haskell.org/package/lispparser-0.2.1 ,
-- written by Jonathan Tang and maintained by Eric Kow.
-- It is released under BSD3, hence, this module is licensed under BSD3.

#ifdef TEST_Z3PP
module Main where
#else
module HipSpec.ATP.Z3ProofParser (z3proofParser,prettyInsts,Insts,Inst(..)) where

import qualified HipSpec.Lang.Simple as S
import HipSpec.Lang.ToPolyFOL as P
import HipSpec.Pretty
import HipSpec.Lang.Renamer
import HipSpec.Property.Repr
import HipSpec.Id
#endif

import Data.Foldable (Foldable)
import Data.Traversable (Traversable,traverse)

import Data.Functor
import Data.List

import Data.Generics.Geniplate

import Control.Applicative hiding (many)
import Text.ParserCombinators.Parsec hiding (spaces,(<|>))

import Control.Monad

data Expr' a
  = Atom a
  | List [Expr' a]
  | Number Integer
 deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

appExpr :: Expr' a -> [Expr' a] -> Expr' a
appExpr e es = List (e:es)

type Expr = Expr' String

instanceUniverseBi [t| forall a . (Expr' a,Expr' a) |]
instanceUniverseBi [t| forall a . (Expr' a,[Expr' a]) |]
instanceTransformBi [t| forall a . (Expr' a,Expr' a) |]

-- | Just labels, for instance properties that don't have
--   any variables (!)
getLabels :: Expr -> [String]
getLabels e0 = nub
  [ s
  | Atom lbl:Atom s:_ <- universeBi e0
  , lbl `elem` [":lblneg",":lblpos"]
  ]

-- | Labels that had a name that was actually an expression
--   (escaped with |{ ... }|, see parseEscaped
getExprLabels :: Expr -> [Expr]
getExprLabels e0 = nub
  [ l
  | Atom lbl:l@List{}:_ <- universeBi e0
  , lbl `elem` [":lblneg",":lblpos"]
  ]

getLets :: Expr -> [(String,Expr)]
getLets e =
  [ (name, val)
  | List (Atom "let":List binders:_) <- universeBi e
  , List [Atom name, val] <- binders
  ]

-- | Get the instantiated quantifiers
getQuantInst :: (Expr -> Expr) -> Expr -> [(Expr,[Expr])]
getQuantInst i e =
  [ (q,map i args)
  | List
     [ List (Atom "_":Atom "quant-inst":args)
     , disj -- is (indirectly) something like: List [Atom "or", Atom q1, Atom q2]
     ] <- universeBi e
  , let List [Atom "or", List [Atom "not", q], _] = i disj
  ]

-- | Gets the quantifier id.
--     Strings: property names
--     Expression: lambdas of the induction hypothesis
getQID :: Expr -> Either String Expr
getQID e = case e of
  List [Atom "forall",_bvars,List (Atom "!":_term:kvs)] | Just qid <- find_qid kvs -> qid
  _ -> error $ "Failed to get qid from " ++ show e
 where
  find_qid (Atom ":qid":Atom qid:_) = Just (Left qid)
  find_qid (Atom ":qid":l@List{}:_) = Just (Right l)
  find_qid (_:xs) = find_qid xs
  find_qid _ = Nothing

-- | Inline/substitution
inline :: Eq a => Bool -> [(a, Expr' a)] -> Expr' a -> Expr' a
inline rec su = transform $ \ e0 -> case e0 of
  Atom s | Just e <- lookup s su -> if rec then inline rec su e else e
  _ -> e0

data Inst e = InstString String [e] | InstExpr e
 deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

rawZ3proofParser :: String -> [Inst Expr]
rawZ3proofParser s =
  case parse parseExpr "proof" s of
    Left e  -> error $ "Z3 proof parser: " ++ show e
    Right p ->
      let lbls = getLabels p
          elbls = getExprLabels p
          lets = getLets p
          quants = getQuantInst (inline True lets) p
      in  [ (InstString l []) | l <- lbls ] ++
          [ InstExpr e | e <- elbls ] ++
          [ either InstString (\ e es -> InstExpr (appExpr e es)) (getQID q) args | (q,args) <- quants ]

symbol :: Parser Char
symbol = oneOf "!$%&*+-/:<=>?@^_~#"

pipe :: Parser Char
pipe = char '|'

spaces :: Parser ()
spaces = skipMany space

parseBrack :: Parser Expr
parseBrack = do
  void (char '{')
  x <- many (noneOf "}")
  void (char '}')
  return (Atom x)

parseEscaped :: Parser Expr
parseEscaped = do
  void (string "|{")
  e <- parseExpr
  void (string "}|")
  return e

parseAtom :: Parser Expr
parseAtom = Atom <$>
  ((:) <$> (letter <|> symbol) <*> many (pipe <|> letter <|> digit <|> symbol))

parseNumber :: Parser Expr
parseNumber = (Number . read) <$> many1 digit

parseList :: Parser Expr
parseList = List <$> sepBy parseExpr (try spaces <|> return ())

parseQuoted :: Parser Expr
parseQuoted = do
  void (char '\'')
  x <- parseExpr
  return $ List [Atom "quote", x]

parseExpr :: Parser Expr
parseExpr = parseAtom
        <|> parseBrack
        <|> parseEscaped
        <|> parseNumber
        <|> parseQuoted
        <|> do void (char '(')
               spaces
               x <- parseList
               spaces
               void (char ')')
               spaces
               return x

printSummary :: forall e . (e -> String) -> [Inst e] -> String
printSummary pp = unlines . map summary
 where
  summary :: Inst e -> String
  summary (InstString s es) = s ++ ": " ++ intercalate ", " (map pp es)
  summary (InstExpr e)      = pp e

#ifdef TEST_Z3PP

printLikeHaskell :: Expr -> String
printLikeHaskell = go
 where
  go e = case e of
    Atom s   -> s
    List [Atom ('p':'r':'o':'j':'_':i:'_':f), List (Atom g:args)]
      | f == g -> go (args !! read [i])
    List es  -> "(" ++ intercalate " " (map go es) ++ ")"
    Number i -> show i

main :: IO ()
main = putStrLn . printSummary printLikeHaskell . rawZ3proofParser =<< getContents

#else

type Insts = [Inst (S.Expr LogicId)]

z3proofParser :: (String -> LogicId) -> String -> Insts
z3proofParser unname = map (fmap go) . rawZ3proofParser
 where
  go :: Expr -> S.Expr LogicId
  go e0 = case e0 of
    Atom s -> var (unname s)
    List [Atom (unname -> P.App),a,b] -> go a `S.App` go b

    -- Known projection: Cons_0 (Cons x xs) = x
    List [Atom (unname -> P.Proj f i),List (Atom (unname -> P.Id g):args)]
      | f == g -> go (args !! i)

    -- Beta reduction. This could be reduced as a rich expression.  Another
    -- idea is to store the RichToSimple transformations inside the Id to
    -- be able to recover them here, let's wait for a use case.
    List (List (Atom (unname -> P.Lambda):vars_body):args)
      | let vars = map (\ (Atom a) -> a) (init vars_body)
      , let body = last vars_body
      , True <- length vars == length args
      -> go (inline False (zip vars args) body)

    List (e:es) -> S.apply (go e) (map go es)
    List [] -> error "printLikeHaskell: empty list?"
    Number i -> S.Lit i

  -- lcl/gbl does not matter, nor type
  var s = S.Lcl s S.Integer

prettyInsts :: Insts -> String
prettyInsts = printSummary exprRepr . evalRenameM (disambig string_var) [] . mapM (traverse rename)
 where
  string_var :: LogicId -> String
  string_var i = case i of
    P.Id v     -> originalId v
    P.Ptr v    -> originalId v
    P.IH       -> "IH"
    P.Proj k n -> "p" ++ show n ++ "{" ++ originalId k ++ "}"
    _          -> "{printLikeHaskell: " ++ show i ++ "}"

#endif
