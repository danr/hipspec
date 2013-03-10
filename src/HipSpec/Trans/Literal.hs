module HipSpec.Trans.Literal (trLiteral) where

import HipSpec.Trans.Property as Prop

import Halo.FOL.Abstract hiding (Term)
import Halo.ExprTrans
import Halo.Monad
import Halo.MonoType

trLiteral :: Literal -> HaloM Formula'
trLiteral l = case l of
    Total t e -> do
        e' <- trExpr e
        monoty <- monoType t
        return (total monoty e')

    e1 :== e2 -> do
        e1' <- trExpr e1
        e2' <- trExpr e2
        return (e1' === e2')

