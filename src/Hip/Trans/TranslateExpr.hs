{-# LANGUAGE ViewPatterns #-}
module Hip.Trans.TranslateExpr where

import Hip.Trans.Core
import Hip.Trans.Monad
import Language.TPTP hiding (Decl,Var)
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

-- | Translate an expression to a term
translateExpr :: Expr -> TM Term
translateExpr (Var n) = applyFun n []
translateExpr e = applyFun (exprName e) =<< mapM translateExpr (exprArgs e)

-- | Apply a function/constructor name to an argument list
--   Follows the function definition if it is an indirection
--   Notice that this function works well on an empty argument list
applyFun :: Name -> [Term] -> TM Term
applyFun n as = do
  b <- lookupName n
  case b of
    QuantVar x        -> return (appFold (T.Var x) as)
    Indirection e     -> (`appFold` as) <$> translateExpr e
    (boundName -> fn) -> do
      arity <- lookupArity n
      if length as < arity
        then -- Partial application
          do useFunPtr n
             return $ appFold (T.Fun (makeFunPtrName fn) []) as
        else -- Function has enough arguments, and could possibly have more
          do -- (for functions returning functions)
             when (boundCon b && length as > arity) $ error $ "Internal error:"
                 ++ " constructor " ++ n ++ "applied to too many arguments."
             return $ appFold (T.Fun fn (take arity as)) (drop arity as)
