-- | Local variables are (sloppily) tagged as Ptrs in the translation
-- from Simple to FunctionalFO, this remedies the situation
-- (it is done in this extra pass to simplify the first translation)
module UnPtrLocalFO where

import Control.Monad.Reader
import Control.Applicative

import Scope
import FunctionalFO

type UPL v a = Reader (Scope v) a

uplFun :: Ord v => Function v -> Function v
uplFun fn = fn
    { fn_body
        = runReader
            (uplBody (fn_body fn))
            (makeScope (map fst (fn_args fn)))
    }

uplBody :: Ord v => Body v -> UPL v (Body v)
uplBody b0 = case b0 of
    Case e alts -> Case <$> uplExpr e <*> mapM uplAlt alts
    Body b      -> Body <$> uplExpr b

uplAlt :: Ord v => Alt v -> UPL v (Alt v)
uplAlt (p,b) = (,) p <$> uplBody b

uplExpr :: Ord v => Expr v -> UPL v (Expr v)
uplExpr e0 = case e0 of
    Ptr x ts      -> do
        b <- inScope x
        return $ if b then Fun x ts [] else e0
    App t1 t2 e1 e2 -> App t1 t2 <$> uplExpr e1 <*> uplExpr e2
    Fun x ts as     -> Fun x ts <$> mapM uplExpr as
    Lit{}           -> return e0

