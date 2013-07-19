module HipSpec.Pretty where

import Text.PrettyPrint
import HipSpec.Lang.PrettyAltErgo

import HipSpec.Utils.ZEncode

import qualified HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.PrettyRich as R
import qualified HipSpec.Lang.PrettyUtils as P

import HipSpec.Lang.ToPolyFOL (Poly(..))
import HipSpec.Lang.PolyFOL (Clause(..))

import HipSpec.Lang.RichToSimple (Rename(..),Loc(..))
import HipSpec.Lang.Type (Typed(..))

import Name
import Unique
import HipSpec.GHC.Utils

type Name' = Rename Name

type TypedName' = Typed Name'

type LogicId = Poly Name'

simpKit :: P.Kit TypedName'
simpKit = let k = text . ppRename . S.forget_type in (k,k)

typeKit :: P.Kit TypedName'
typeKit = let k = parens . R.ppTyped (text . ppRename) in (k,k)

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

-- | Printing names
polyname :: Poly (Name') -> String
polyname x0 = case x0 of
    Id x     -> ppRename x
    Ptr x    -> ppRename x ++ "_ptr"
    App      -> "app"
    TyFn     -> "fn"
    Proj x i -> "proj_" ++ show i ++ "_" ++ ppRename x
    QVar i   -> 'x':show i

ppName :: Name -> String
ppName nm = getOccString nm ++ '_': showOutputable (getUnique nm)

ppRename :: Name' -> String
ppRename (Old nm)   = ppName nm
ppRename (New ls x) = concatMap ((++ "_") . loc) ls ++ show x
  where
    loc :: Loc (Name') -> String
    loc lc = case lc of
        CaseLoc   -> "case"
        LamLoc    -> "lambda"
        LetLoc nm -> ppRename nm

ppAltErgo :: [Clause LogicId] -> String
ppAltErgo = render . vcat . map (ppClause (text . zencode . polyname))

