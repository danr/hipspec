module Hip.Trans.Names where

import Hip.Trans.Core

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

projName :: Name -> Int -> Name
projName tn i = tn ++ "_p" ++ show i

projExpr :: Name -> Int -> Expr -> Expr
projExpr tn i e = App (projName tn i) [e]

proj :: Name -> Int -> Term -> Term
proj tn i t = Fun (FunName (projName tn i)) [t]

simpProjCon :: Name -> Term -> Name -> Int -> Term
simpProjCon tn t c n = Fun (FunName c) [ proj tn i t | i <- [0..n-1] ]
