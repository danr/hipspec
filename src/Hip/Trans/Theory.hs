{-# LANGUAGE RecordWildCards #-}
module Hip.Trans.Theory where

import Halo.Subtheory
import Hip.Trans.Property

import CoreSyn
import Var
import Type
import TysWiredIn
import TyCon
import DataCon
import Outputable
import Halo.FOL.Abstract hiding (Lemma)
import qualified Halo.FOL.Abstract as A

import Halo.Data (f,f',x,x',varNames)

data HipSpecExtras
    = Lemma String
    -- ^ Lemma with a name
    | Typing TyCon
    -- ^ Type predicates for a data type (not yet implemented)
    | PrimMinRec
    -- ^ [hipspec only] Base theory about minrec
    | MinRec TyCon
    -- ^ [hipspec only] Recursive min for a data type
  deriving
    (Eq,Ord)

makeDataDepend :: HipSpecSubtheory -> HipSpecSubtheory
makeDataDepend s@(Subtheory{..}) = case provides of
    Data ty_con -> s { depends = Specific (MinRec ty_con) : depends }
    _           -> s

mkMinRec :: [TyCon] -> [HipSpecSubtheory]
mkMinRec ty_cons =
    [ let minrec_formulae =
              [ forall' xs $ minrec kxs ==> min' xi
              | c <- cons
              , let k               = dataConWorkId c
                    (_,_,ty_args,_) = dataConSig c
                    arity           = length ty_args
                    xs              = take arity varNames
                    kxs             = apply k (map qvar xs)
              , i <- [0..arity-1]
              -- ^ vacuous if arity == 0
              , let xi              = qvar (xs !! i)
              ]

      in  Subtheory
              { provides    = Specific (MinRec ty_con)
              , depends     = [Specific PrimMinRec]
              , description = "minrec for " ++ showSDoc (pprSourceTyCon ty_con)
              , formulae    = minrec_formulae
              }

    | ty_con <- ty_cons
    , let DataTyCon cons _ = algTyConRhs ty_con
    ]
      ++
    [ Subtheory
         { provides    = Specific PrimMinRec
         , depends     = []
         , description = "minrec implies min, and minrec on app"
         , formulae    =
                [ forall' [x]   $ minrec x' ==> min' x'
                , forall' [f,x] $ minrec (app f' x') ==> min' f'
                , forall' [f,x] $ minrec (app f' x') ==> min' x'
                ]
         }
    ]

-- Make datatypes depend on MinRec (or vice versa, or something)
-- [ MinRec ty_con | use_minrec ]

instance Show HipSpecExtras where
    show (Lemma s)   = "Lemma " ++ s
    show (Typing tc) = "Typing predicate"

instance Clausifiable HipSpecExtras where
    mkClause (Lemma s) = A.namedClause ("Lemma{" ++ s ++ "}") A.Lemma
    mkClause _         = A.clause A.Axiom

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras

data Theory = Theory { subthys :: [HipSpecSubtheory] }
