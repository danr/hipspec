module HipSpec.Trans.Literal (trLiteral) where

import HipSpec.Trans.Property as Prop

import Halo.FOL.Abstract hiding (Term)
import Halo.ExprTrans
import Halo.Monad

-- The terms returned are terms appropriate to do min on
trLiteral :: Literal -> HaloM (Formula',[Term'])
trLiteral l = case l of
    Total e -> do
        e' <- trExpr e
        return (cf e',[e'])

    e1 :== e2 -> do
        e1' <- trExpr e1
        e2' <- trExpr e2
        return (e1' === e2',[e1',e2'])

