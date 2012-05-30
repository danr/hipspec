{-# LANGUAGE DoRec #-}
module Hip.Trans.ParserInternals
       (declsGrammar
       ,parseDecls
       ,parseBranch
       ,parsePattern
       ,parseExpr
       ,parseType
       )
       where

import Data.Parser.Grempa.Grammar
import Data.Parser.Grempa.Dynamic
import Data.Data

import qualified Hip.Trans.Lexer as L
import Hip.Trans.Core
import Hip.Trans.Pretty

parseFromGrammar :: Data e => Grammar L.Tok e -> String -> e
parseFromGrammar g = parse (mkDynamicParser constrWrapper g) . L.lex

parseDecls :: String -> [Decl]
parseDecls = parseFromGrammar declsGrammar

parseBranch :: String -> Branch
parseBranch = parseFromGrammar branchGrammar

parsePattern :: String -> Pattern
parsePattern = parseFromGrammar (patternGrammar False)

parseExpr :: String -> Expr
parseExpr = parseFromGrammar exprGrammar

parseType :: String -> Type
parseType = parseFromGrammar (tyGrammar False)

lg :: Grammar L.Tok Name
lg = rule [ L.fromTok <@> L.lident ]

ug :: Grammar L.Tok Name
ug = rule [ L.fromTok <@> L.uident ]

exprGrammar :: Grammar L.Tok Expr
exprGrammar = do
  rec
    l   <- lg
    u   <- ug

    e   <- rule [ app  <@> e <#> e2
                , id   <@> e2
                ]
    e2  <- rule [ con0 <@> u
                , Var  <@> l
                , id   <@  L.LPar <#> e <# L.RPar ]
  return e

patternGrammar :: Bool -> Grammar L.Tok Pattern
patternGrammar parens = do
  rec
    l   <- lg
    u   <- ug

    p   <- rule [ PCon  <@> u <#> p2s
                , id    <@> p2 ]
    p2  <- rule [ PVar  <@> l
                , pcon0 <@> u
                , id    <@  L.LPar <#> p <# L.RPar ]
    p2s <- several p2

  if parens then return p2
            else return p

branchGrammar :: Grammar L.Tok Branch
branchGrammar = do
  let (-->) :: Pattern -> (Maybe Expr,Expr) -> Branch
      p --> (Just g ,e) = Guard p g :-> e
      p --> (Nothing,e) = NoGuard p :-> e
  rec
    p   <- patternGrammar False
    e   <- exprGrammar
    g   <- rule [ (,) Nothing <@ L.Arrow <#> e
                , (,) . Just  <@ L.Bar   <#> e <# L.Arrow <#> e ]
    br  <- rule [ (-->) <@> p <#> g ]

  return br

tyGrammar :: Bool -> Grammar L.Tok Type
tyGrammar parens = do
  rec
    l   <- lg
    u   <- ug
    t   <- rule [ tapp <@> t2 <# L.Arrow <#> t
                , id   <@> t2
                ]
    t2  <- rule [ TyCon <@> u <#> t3s
                , id    <@> t3
                ]
    t3  <- rule [ TyVar  <@> l
                , tycon0 <@> u
                , id    <@  L.LPar <#> t <# L.RPar
                ]
    t3s <- several t3
  if parens then return t3
            else return t

declsGrammar :: Grammar L.Tok [Decl]
declsGrammar = do
  rec
    l   <- lg
    u   <- ug
    ls0 <- several0 l

    pp   <- patternGrammar True
    pps0 <- several0 pp

    ts  <- several0 =<< tyGrammar True
    c   <- rule [ Cons <@> u <#> ts ]
    cs  <- severalInter L.Bar c

    d   <- rule [ func <@> l <#> pps0 <# L.Eq <#> b <# L.Semi
                , Data <@  L.Data <#> u <#> ls0 <# L.Eq <#> cs <# L.Semi
                , TyDecl <@> l <# L.DoubleColon <#> t <# L.Semi  -- conflict?
                ]
    ds  <- several d

    b   <- rule [ Case <@  L.Case <#> e <# L.Of <# L.LBrace <#> brs <# L.RBrace
                , Expr <@> e ]

    e   <- exprGrammar

    t   <- tyGrammar False

    br  <- branchGrammar
    brs <- severalInter L.Semi br

  return ds

