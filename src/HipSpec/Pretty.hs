{-# LANGUAGE PatternGuards #-}
module HipSpec.Pretty where

import Text.PrettyPrint
import HipSpec.Lang.PrettyAltErgo

import HipSpec.Utils.ZEncode

import HipSpec.Lang.Renamer

import qualified HipSpec.Lang.Rich as R
import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.PrettyRich as R
import qualified HipSpec.Lang.PrettyUtils as P

import HipSpec.Lang.ToPolyFOL (Poly(..))
import HipSpec.Lang.PolyFOL (Clause(..))

import HipSpec.Lang.RichToSimple (Rename(..),Loc(..))
import HipSpec.Lang.Type (Typed(..))

import Data.List (intercalate)

import HipSpec.GHC.Utils

import BasicTypes (TupleSort(..))
import Name
import PrelNames

type Name' = Rename Name

type TypedName' = Typed Name'

type LogicId = Poly Name'

richKit :: P.Kit (Typed Name)
richKit = let k = text . ppName . S.forget_type in (k,k)

simpKit :: P.Kit TypedName'
simpKit = let k = text . ppRename . S.forget_type in (k,k)

typeKit :: P.Kit TypedName'
typeKit = let k = parens . R.ppTyped (text . ppRename) in (k,k)

showRich :: R.Function (Typed Name) -> String
showRich = render . R.ppFun richKit

showSimp :: S.Function TypedName' -> String
showSimp = render . R.ppFun simpKit . S.injectFn

showExpr :: S.Expr TypedName' -> String
showExpr = render . R.ppExpr 0 simpKit . S.injectExpr

showTypedExpr :: S.Expr TypedName' -> String
showTypedExpr = render . R.ppExpr 0 typeKit . S.injectExpr

showBody :: S.Body TypedName' -> String
showBody = render . R.ppExpr 0 simpKit . S.injectBody

showType :: S.Type Name' -> String
showType = render . R.ppType 0 (text . ppRename)

showTyped :: Typed Name' -> String
showTyped = render . R.ppTyped (text . ppRename)

-- | Printing names
polyname :: LogicId -> String
polyname x0 = case x0 of
    Id x     -> ppRename x
    Ptr x    -> ppRename x ++ "_ptr"
    App      -> "app"
    TyFn     -> "Fn"
    Proj x i -> "proj_" ++ show i ++ "_" ++ ppRename x
    QVar i   -> 'x':show i

ppName :: Name -> String
ppName nm -- = getOccString nm {- ++ '_': showOutputable (getUnique nm) -}
    | k == listTyConKey      = "List"
    | k == listTyConKey      = "List"
    | k == nilDataConKey     = "Nil"
    | k == consDataConKey    = "Cons"
    | k == unitTyConKey      = "UnitTyCon"
    | k == genUnitDataConKey = "Unit"
    | Just (ns, ts, n) <- isTupleOcc_maybe (getOccName nm) = name_tuple ns ts n
    | otherwise = case getOccString nm of
        "+"   -> "plus"
        "-"   -> "minus"
        "/"   -> "div"
        "*"   -> "mult"
        "^"   -> "pow"
        "++"  -> "append"
        ">>=" -> "bind"
        "=<<" -> "dnib"
        ">=>" -> "dot_monadic"
        "<=<" -> "monadic_dot"
        "<*>" -> "ap"
        "<$>" -> "fmap"
        ">>"  -> "then"
        "||"  -> "or"
        "&&"  -> "and"
        "."   -> "dot"
        "=="  -> "equal"
        "/="  -> "unequal"
        ">"   -> "gt"
        ">="  -> "ge"
        "<"   -> "lt"
        "<="  -> "le"
        "$"   -> "apply"
        "!!"  -> "index"
        "\\\\" -> "difference"
        s     -> s -- ++ '_': showOutputable (getUnique nm)
  where
    k = getUnique nm

    name_tuple ns ts n = pre ++ mid ++ show n
      where
        pre | ns == tcName   = "T"
            | ns == dataName = "t"
            | otherwise      = portableShowSDoc (pprNameSpace ns)

        mid = case ts of
            BoxedTuple   -> ""
            UnboxedTuple -> "u"
            _            -> "unknown_tuple"

ppRename :: Name' -> String
ppRename (Old nm)    = ppName nm
ppRename Bottom      = "bottom"
ppRename (New [LamLoc] _) = "eta"
ppRename (New [] _)       = "x"
ppRename (New ls _x) = intercalate "_" (map loc ls)
  where
    loc :: Loc Name' -> String
    loc lc = case lc of
        CaseLoc   -> "case"
        LamLoc    -> "lambda"
        LetLoc nm -> ppRename nm

ppAltErgo :: [Clause LogicId] -> String
ppAltErgo
    = render . vcat . map (ppClause text) . renameCls

renameCls :: [Clause LogicId] -> [Clause String]
renameCls = runRenameM (zencode . polyname) altErgoKeywords . mapM rename

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

