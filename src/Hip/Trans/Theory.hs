module Hip.Trans.Theory where

import Halt.Subtheory

import CoreSyn
import Var
import Type
import TysWiredIn

import qualified Test.QuickSpec.Term as QST

data Theory = Theory { subthys :: [Subtheory] }

data Prop = Prop
    { proplhs     :: CoreExpr
    , proprhs     :: CoreExpr
    , propVars    :: [(Var,Type)]
    , propName    :: String
    , propRepr    :: String
    , propQSTerms :: (QST.Term QST.Symbol,QST.Term QST.Symbol)
    , propDeps    :: [Var]
    , propOops    :: Bool
    -- ^ It's an error if this property was provable
    }

inconsistentProp :: Prop
inconsistentProp = Prop
    { proplhs     = Var trueDataConId
    , proprhs     = Var falseDataConId
    , propVars    = []
    , propName    = "inconsistencyCheck"
    , propRepr    = "inconsistecy check: this should never be provable"
    , propQSTerms = error "propQSTerms: inconsistentProp"
    , propDeps    = []
    , propOops    = True
    }
