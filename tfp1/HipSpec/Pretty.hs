module HipSpec.Pretty where

import Text.PrettyPrint
import Lang.PrettyAltErgo

import Lang.Escape

import qualified Lang.Simple as S
import qualified Lang.PrettyRich as R
import qualified Lang.PrettyUtils as P

import Lang.ToPolyFOL (Poly(..))
import Lang.PolyFOL (Clause(..))

import Lang.RichToSimple (Rename(..),Loc(..))
import Lang.Type (Typed(..))

import Name
import Unique
import Lang.Utils

type Name' = Rename Name

type TypedName' = Typed Name'

type LogicId = Poly Name'

simpKit :: P.Kit TypedName'
simpKit = let k = text . ppRename . S.forget_type in (k,k)

showSimp :: S.Function TypedName' -> String
showSimp = render . R.ppFun simpKit . S.injectFn

showExpr :: S.Expr TypedName' -> String
showExpr = render . R.ppExpr 0 simpKit . S.injectExpr

showBody :: S.Body TypedName' -> String
showBody = render . R.ppExpr 0 simpKit . S.injectBody

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
ppAltErgo = render . vcat . map (ppClause (text . escape . polyname))

