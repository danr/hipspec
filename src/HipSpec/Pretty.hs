{-# LANGUAGE PatternGuards,OverloadedStrings,ViewPatterns #-}
module HipSpec.Pretty where

import Text.PrettyPrint
import qualified HipSpec.Lang.PrettyAltErgo as AltErgo
import qualified HipSpec.Lang.PrettyTFF as TFF
import qualified HipSpec.Lang.PrettySMT as SMT

import HipSpec.Lang.Renamer

import HipSpec.Lang.Monomorphise

import qualified HipSpec.Lang.Rich as R
import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.PrettyRich as R
import HipSpec.Lang.PrettyUtils (Types(..),PP(..))

import HipSpec.Lang.ToPolyFOL (Poly(..))
import HipSpec.Lang.PolyFOL (Clause(..))
import qualified HipSpec.Lang.PolyFOL as P
import qualified HipSpec.Lang.ToPolyFOL as P

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import Control.Arrow (second)

import HipSpec.Id

import Data.Char

import PrimOp

type LogicId = Poly Id

docId :: Id -> Doc
docId = text . ppId

showSimp :: S.Function Id -> String
showSimp = render . R.ppFun Show docId . S.injectFn

showRich :: R.Function Id -> String
showRich = render . R.ppFun Show docId

showExpr :: S.Expr Id -> String
showExpr = render . R.ppExpr 0 Don'tShow docId . S.injectExpr

showBody :: S.Body Id -> String
showBody = render . R.ppExpr 0 Don'tShow docId . S.injectBody

showType :: S.Type Id -> String
showType = render . R.ppType 0 docId

showPolyType :: S.PolyType Id -> String
showPolyType = render . R.ppPolyType docId

showTyped :: (Id,S.Type Id) -> String
showTyped (v,t) = render (hang (docId v <+> "::") 2 (R.ppType 0 docId t))

-- | Printing names
polyname :: LogicId -> String
polyname x0 = case x0 of
    Id x     -> ppId x
    Ptr x    -> ppId x ++ "_ptr"
    App      -> "app"
    TyFn     -> "Fn"
    Proj x i -> "proj_" ++ show i ++ "_" ++ ppId x
    QVar i   -> 'x':show i
    IH       -> "IH"
    P.Lambda -> "lambda"
    SK a b   -> "sk" ++ polyname a ++ show b

mononame :: IdInst LogicId LogicId -> String
mononame (IdInst x xs) = polyname x -- ++ short (concatMap (\ u -> '_':ty u) xs)
  where
    {-
    ty (P.TyCon TyFn [u,v]) = "q" ++ ty u ++ "_" ++ ty v ++ "p"
    ty (P.TyCon i []) = polyname i
    ty (P.TyCon i is) = "q" ++ polyname i ++ concatMap (\ u -> '_':ty u) is ++ "p"
    -}
    ty (P.TyCon i is) = polyname i ++ concatMap (\ u -> '_':ty u) is
    ty (P.TyVar i)    = polyname i
    ty P.Integer      = "int"
    ty P.TType        = "type"

render' :: Doc -> String
render' = renderStyle style { lineLength = 150 }

renameCls :: (Ord a,Ord b) =>
    [String] -> [(a,String)] -> (a -> String) -> (b -> String) -> [Clause a b] -> ([Clause String String],Map (Either a b) String)
renameCls kwds alloc f g = runRenameM (disambig2 f g) kwds alloc' . mapM renameBi2
  where alloc' = M.fromList [(Left x,s) | (x,s) <- alloc]

prettyCls :: (Ord a,Ord b) => (PP String String -> Clause String String -> Doc) -> [String]
             -> [(a,String)]
             -> (a -> String) -> (b -> String)
             -> [Clause a b] -> (String,Map String (Either a b))
prettyCls pp kwds alloc f g cls0 =
    ( render' . vcat . map (pp ppText) $ cls
    , M.fromList [ (s,i) | (i,s) <- M.toList rename_map ]
    )
  where
    (cls,rename_map) = renameCls kwds alloc f g cls0

prettyTPTP :: (Show a,Ord a,Ord b) => [(a,String)] -> (a -> String) -> (b -> String) -> [Clause a b] -> String
prettyTPTP prims symb var = fst . prettyCls TFF.ppClause tptpKeywords prims symb' var'
  where
    -- TPTP: A-Za-Z0-9_ are allowed,
    -- but initial has to be A-Z_ for variables, and a-z0-9 for symbols
    -- (General strings could be allowed for symbols, enclosed in '')
    var' x = case escape (var x) of
        u:us | isLower u -> toUpper u:us
             | isDigit u || u == '_' -> 'X':u:us
             | otherwise -> u:us
        []               -> "X"

    symb' x = case dropWhile (== '_') (escape (symb x)) of
        u:us | isUpper u -> toLower u:us
             | otherwise -> u:us
        []               -> "a"

ppText :: PP String String
ppText = PP text text

ppTHF :: [Clause LogicId LogicId] -> String
ppTHF = prettyTPTP thfPrims polyname polyname

ppTFF :: [Clause (IdInst LogicId LogicId) LogicId] -> String
ppTFF = prettyTPTP tffPrims mononame polyname

ppAltErgo :: [Clause LogicId LogicId] -> String
ppAltErgo = fst . prettyCls AltErgo.ppClause altErgoKeywords altErgoPrims (escape . polyname) (escape . polyname)

ppMonoAltErgo :: [Clause (IdInst LogicId LogicId) LogicId] -> String
ppMonoAltErgo = fst . prettyCls AltErgo.ppClause altErgoKeywords altErgoMonoPrims (escape . mononame) (escape . polyname)

ppSMT :: [Clause (IdInst LogicId LogicId) LogicId] -> (String,Map String LogicId)
ppSMT = second (M.map (either forget_inst id)) . prettyCls SMT.ppClause smtKeywords smtPrims (escape . mononame) (escape . polyname)

altErgoPrims,thfPrims :: [(LogicId,String)]
altErgoPrims = []
thfPrims = []

altErgoMonoPrims,tffPrims,smtPrims :: [(IdInst LogicId LogicId,String)]
altErgoMonoPrims = []
tffPrims = []
smtPrims =
    [ (IdInst (Id (GHCPrim op)) [],s)
    | (op,s) <-
        [ (IntAddOp,"+") ]
    ]



tptpKeywords :: [String]
tptpKeywords = smtKeywords ++
    [ "fof", "cnf", "tff" ]

smtKeywords :: [String]
smtKeywords = altErgoKeywords ++
    [ "Bool", "Int", "Array", "List", "head", "tail", "nil", "insert"
    , "assert", "check-sat"
    , "abs", "min", "max", "const"
    -- CVC4:
    , "as", "concat"
    ]

altErgoKeywords :: [String]
altErgoKeywords =
    [ "ac"
    , "and"
    , "axiom"
    , "inversion"
    , "bitv"
    , "bool"
    , "check"
    , "cut"
    , "distinct"
    , "else"
    , "exists"
    , "false"
    , "forall"
    , "function"
    , "goal"
    , "if"
    , "in"
    , "include"
    , "int"
    , "let"
    , "logic"
    , "not"
    , "or"
    , "predicate"
    , "prop"
    , "real"
    , "rewriting"
    , "then"
    , "true"
    , "type"
    , "unit"
    , "void"
    , "with"
    ]

escape :: String -> String
escape = leading . concatMap (\ c -> fromMaybe [c] (M.lookup c escapes))
  where
    escapes = M.fromList
        [ (from,'_':to++"_")
        | (from,to) <-
            [ ('(',"rpar")
            , (')',"lpar")
            , (':',"cons")
            , ('[',"rbrack")
            , (']',"lbrack")
            , (',',"comma")
            , ('`',"tick")

            , ('}',"rbrace")
            , ('{',"lbrace")

            , ('\'',"prime")
            , ('@',"at")
            , ('!',"bang")
            , ('%',"percent")
            , ('$',"dollar")
            , ('=',"equal")
            , (' ',"space")
            , ('>',"gt")
            , ('#',"hash")
            , ('|',"pipe")
            , ('^',"hat")
            , ('-',"dash")
            , ('&',"and")
            , ('.',"dot")
            , ('+',"plus")
            , ('?',"qmark")
            , ('*',"star")
            , ('~',"twiggle")
            , ('/',"slash")
            , ('\\',"bslash")
            , ('<',"lt")
            ]
        ]

    leading :: String -> String
    leading xs@(x:_) | isDigit x = '_':xs
                     | otherwise = xs
    leading []                   = "_"

