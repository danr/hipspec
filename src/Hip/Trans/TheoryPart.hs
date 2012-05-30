module Hip.Trans.TheoryPart where

import Hip.Trans.Core
import qualified Language.TPTP as T

data Theory = Theory { thyFuns  :: [ThyFun]
                     , thyDatas :: [Decl]
                     -- ^ Invariant: all are data declarations
                     }

data ThyFun = ThyFun { funcName :: Name
                     , funcTPTP :: [T.Decl]
                     , funcPtrs :: [Name]     -- Function ptrs this uses
                     , funcFunDeps  :: [Name] -- Func defs this function uses
                     , funcDataDeps :: [Name] -- Data defs this function uses
                     , funcType :: Maybe Type
                     }

data Prop = Prop { lhs :: Expr  -- this might change to
                 , rhs :: Expr
                 }

type TrimmedTheory = Theory

-- | Trims down a theory
trimTheoryByNames :: [Name] -> Theory -> TrimmedTheory
trimTheoryByNames = undefined

-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Theory -> Prop -> [Prop] -> Property
theoryToInvocations = undefined

-- | Is a type finite in a theory?
finiteType :: Theory -> Type -> Bool
finiteType thy n = undefined