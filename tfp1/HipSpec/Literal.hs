module HipSpec.Literal (trLiteral) where

import HipSpec.Theory
import HipSpec.Translate
import HipSpec.Property

import Lang.PolyFOL

trLiteral :: ArityMap -> [Name'] -> Literal -> Formula LogicId
trLiteral am sc (e1 :=: e2) = trSimpExpr am sc e1 === trSimpExpr am sc e2

