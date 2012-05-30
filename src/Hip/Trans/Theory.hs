module Hip.Trans.Theory where

import Hip.Util
import Hip.StructuralInduction (TyEnv)

import Halt.FOL.Abstract

import CoreSyn
import Var
import Type
import TysWiredIn

import qualified Test.QuickSpec.Term as QST

data Theory = Theory { thyDataAxioms :: [AxClause]
                     , thyDefAxioms  :: [VarClause]
                     , thyTyEnv      :: TyEnv Var Type
                     }

data Prop = Prop { proplhs  :: CoreExpr
                 , proprhs  :: CoreExpr
                 , propVars :: [(Var,Type)]
                 , propName :: String
                 , propRepr :: String
                 , propQSTerms :: {- Maybe -} (QST.Term QST.Symbol,QST.Term QST.Symbol)
                 }

inconsistentProp :: Prop
inconsistentProp = Prop { proplhs  = Var trueDataConId
                        , proprhs  = Var falseDataConId
                        , propVars = []
                        , propName = color Red "inconsistencyCheck"
                        , propRepr = "inconsistecy check: this should never be provable"
                        , propQSTerms = error "propQSTerms: inconsistentProp"
                        }

thyFiniteType :: Theory -> Type -> Bool
thyFiniteType = error "thyFiniteType: unimplemented"

