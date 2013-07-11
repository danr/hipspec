-- | Local variables are (sloppily) tagged as Ptrs in the translation
-- from Simple to FunctionalFO, this remedies the situation
-- (it is done in this extra pass to simplify the first translation)
module UnPtrLocalFO where

import Control.Monad.Reader
import Control.Applicative

import Scope
import FunctionalFO

type UPL v a = Reader (Scope (Var v)) a

uplFun :: Ord v => Function (Var v) -> Function (Var v)
uplFun (Function f as b) = flip runReader (makeScope as) $ do
    Function f <$> mapM uplVar as <*> uplBody b

uplVar :: Ord v => Var v -> UPL v (Var v)
uplVar x = do
    b <- inScope x
    return $ case (b,x) of
        (True,Ptr y ::: t) -> Orig y ::: t
        _                  -> x

uplBody :: Ord v => Body (Var v) -> UPL v (Body (Var v))
uplBody b0 = case b0 of
    Case e alts -> Case <$> uplExpr e <*> mapM uplAlt alts
    Body b      -> Body <$> uplExpr b

uplAlt :: Ord v => Alt (Var v) -> UPL v (Alt (Var v))
uplAlt (p,b) = uplPat p (\ p' -> (,) p' <$> uplBody b)

uplPat :: Ord v => Pattern (Var v) -> (Pattern (Var v) -> UPL v a) -> UPL v a
uplPat p k = case p of
    ConPat c ts as -> extendScope as $ do
        as' <- mapM uplVar as
        k (ConPat c ts as')
    LitPat{}   -> k p
    Default -> k p

uplExpr :: Ord v => Expr (Var v) -> UPL v (Expr (Var v))
uplExpr e0 = case e0 of
    Apply x ts as -> Apply <$> uplVar x <*> pure ts <*> mapM uplExpr as
    Lit{}         -> return e0

