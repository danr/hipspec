module HipSpec.Lint where

import Text.PrettyPrint

import HipSpec.Lang.LintRich as R
import HipSpec.Lang.Simple as S

import HipSpec.GHC.Utils

import CoreSyn
import CoreLint
import SrcLoc

import HipSpec.Id
import HipSpec.Pretty (pkId)
import HipSpec.Lang.PrettyUtils (P)

coreExprLint :: CoreExpr -> Maybe String
coreExprLint = fmap portableShowSDoc . lintUnfolding noSrcLoc []

lintRich :: Ord v => P v -> [(v,Type v)] -> LintM v a -> Maybe String
lintRich pk sc m = case lintWithScope sc pk m of
    []   -> Nothing
    errs -> Just (render . vcat $ errs)

lintSimple :: [S.Function Id] -> Maybe String
lintSimple = lintRich pkId [] . lintFns . map injectFn

lintSimpleExpr :: [(Id,Type Id)] -> S.Expr Id -> Maybe String
lintSimpleExpr sc = lintRich pkId sc . R.lintExpr . injectExpr

