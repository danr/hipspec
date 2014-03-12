{-# LANGUAGE PatternGuards,OverloadedStrings #-}
module HipSpec.Pretty where

import Text.PrettyPrint
import HipSpec.Lang.PrettyAltErgo

import HipSpec.Utils.ZEncode

import HipSpec.Lang.Renamer

import HipSpec.Lang.Monomorphise

import qualified HipSpec.Lang.Rich as R
import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.PrettyRich as R
import HipSpec.Lang.PrettyUtils (Types(..),PP(..))

import HipSpec.Lang.ToPolyFOL (Poly(..))
import HipSpec.Lang.PolyFOL (Clause(..))
import qualified HipSpec.Lang.PolyFOL as P

import HipSpec.Id

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

mononame :: IdInst LogicId LogicId -> String
mononame (IdInst x xs) = polyname x ++ concatMap (\ u -> '_':ty u) xs
  where
    ty (P.TyCon i is) = polyname i ++ concatMap (\ u -> '_':ty u) is
    ty (P.TyVar i)    = polyname i
    ty P.Integer      = "int"
    ty P.TType        = "type"

ppAltErgo :: [Clause LogicId LogicId] -> String
ppAltErgo = render . vcat . map (ppClause (PP text text)) . renameCls polyname

ppMonoAltErgo :: [Clause (IdInst LogicId LogicId) LogicId] -> String
ppMonoAltErgo
    = render . vcat . map (ppClause (PP text (text . ("lcl_" ++))))
    . renameCls mononame . map (fmap (`IdInst` []))

renameCls :: Ord v => (v -> String) -> [Clause v v] -> [Clause String String]
renameCls f = runRenameM (disambig (zencode . f)) altErgoKeywords . mapM renameBi

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

