module HipSpec.Lint where

import Text.PrettyPrint

import HipSpec.Lang.LintRich
import HipSpec.Lang.Simple as S
import HipSpec.Pretty

import HipSpec.GHC.Utils

import CoreSyn
import CoreLint
import SrcLoc

coreExprLint :: CoreExpr -> Maybe String
coreExprLint = fmap portableShowSDoc . lintUnfolding noSrcLoc []

lintRich :: Ord v => (v -> String) -> [Typed v] -> LintM v a -> Maybe String
lintRich p sc m = case lintWithScope sc m of
    []   -> Nothing
    errs -> Just (render . vcat . map (ppErr (text . p)) $ errs)

lintSimple :: [S.Function TypedName'] -> Maybe String
lintSimple = lintRich ppRename [] . lintFns . map injectFn

lintSimpleExpr :: [TypedName'] -> S.Expr TypedName' -> Maybe String
lintSimpleExpr sc = lintRich ppRename sc . lintExpr . injectExpr

