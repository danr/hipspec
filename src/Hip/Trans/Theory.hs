module Hip.Trans.Theory where

import Halo.Subtheory

import CoreSyn
import Var
import Type
import TysWiredIn
import TyCon
import qualified Halo.FOL.Abstract as A

import qualified Test.QuickSpec.Term as QST

data HipSpecExtras
    = Lemma String
    -- ^ Lemma with a name
    | Typing TyCon
    -- ^ Type predicates for a data type (not yet implemented)
  deriving
    (Eq,Ord)

instance Show HipSpecExtras where
    show (Lemma s)   = "Lemma " ++ s
    show (Typing tc) = "Typing predicate"

instance Clausifiable HipSpecExtras where
    mkClause (Lemma s) = A.namedClause ("Lemma{" ++ s ++ "}") A.Lemma
    mkClause _         = A.clause A.Axiom

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras

data Theory = Theory { subthys :: [HipSpecSubtheory] }

data Prop = Prop
    { proplhs     :: CoreExpr
    , proprhs     :: CoreExpr
    , propVars    :: [(Var,Type)]
    , propName    :: String
    , propRepr    :: String
    , propQSTerms :: (QST.Term QST.Symbol,QST.Term QST.Symbol)
    , propFunDeps :: [Var]
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
    , propFunDeps = []
    , propOops    = True
    }
