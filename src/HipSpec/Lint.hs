module HipSpec.Lint where

import Text.PrettyPrint

import HipSpec.Lang.LintRich as R
import HipSpec.Lang.Simple as S

import HipSpec.GHC.Utils

import CoreSyn
import CoreLint
import SrcLoc

import HipSpec.Id

coreExprLint :: CoreExpr -> Maybe String
coreExprLint = fmap portableShowSDoc . lintUnfolding noSrcLoc []

lintRich :: Ord v => (v -> String) -> [(v,Type v)] -> LintM v a -> Maybe String
lintRich p sc m = case lintWithScope sc (text . p) m of
    []   -> Nothing
    errs -> Just (render . vcat $ errs)

lintSimple :: [S.Function Id] -> Maybe String
lintSimple = lintRich ppId [] . lintFns . map injectFn

lintSimpleExpr :: [(Id,Type Id)] -> S.Expr Id -> Maybe String
lintSimpleExpr sc = lintRich ppId sc . R.lintExpr . injectExpr

