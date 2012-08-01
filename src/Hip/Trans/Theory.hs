{-# LANGUAGE RecordWildCards #-}
module Hip.Trans.Theory
    ( HipSpecExtras(..)
    , setExtraDependencies
    , mkMinRecAxioms
    , mkDomainAxioms
    , mkResultTypeAxioms
    , HipSpecContent
    , HipSpecSubtheory
    , Theory(..)
    ) where

import CoreSyn
import Var
import Type
import TysWiredIn
import TyCon
import DataCon
import Outputable
import GHC (dataConType)

import Halo.Names
import Halo.Shared
import Halo.Subtheory
import Halo.Trim
import Halo.Util
import Halo.FOL.Abstract

import Hip.Trans.Property
import Hip.Trans.Types
import Hip.Trans.TypeGuards

data HipSpecExtras
    = Lemma String
    -- ^ Lemma with a name
    | Domain TyCon
    -- ^ Domain axiom for a data type + type predicates if finite
    | ResultType Var
    -- ^ If a function f returns a finite type t, this axiom says
    --       forall x1, .., xn . isType(f(x1,..,xn),t)
    | PrimMinRec
    -- ^ [hipspec only] Base theory about minrec
    | MinRec TyCon
    -- ^ [hipspec only] Recursive min for a data type
  deriving
    (Eq,Ord)

-- | Make data types depend on Domain axioms, and MinRec axioms if min is used.
--   Make functions depend on finite result type axioms.
setExtraDependencies :: Bool -> HipSpecSubtheory -> HipSpecSubtheory
setExtraDependencies use_min s@(Subtheory{..}) = case provides of
    Data ty_con -> s { depends = (use_min ? (Specific (MinRec ty_con) :)) $
                                 (Specific (Domain ty_con) : depends)
                     }
    Function f  -> s { depends = Specific (ResultType f) : depends }
    _           -> s

-- | Make an axiom for every function f
--
--      f : t1 -> t2 -> .. -> tn -> tr
--
--   where the result type `tr` is finite, like this:
--
--      ! [X1,..,Xn] . type(f(X1,..,Xn),tr)
mkResultTypeAxioms :: [CoreBind] -> [HipSpecSubtheory]
mkResultTypeAxioms binds =
    [ let (args_ty,res_ty)  = splitFunTys (repType (varType f))
          us                = zipWith setVarType varNames args_ty
          fus               = apply f (map qvar us)
          (ty_qs,res_ty_tm) = trType res_ty
          res_ty_formulae   =
              [ forall' (ty_qs ++ us) $ min' fus ==> isType fus res_ty_tm
              | finiteType res_ty
              ]
      in  Subtheory
              { provides    = Specific (ResultType f)
              , depends     = []
              , description = "Result type axiom for " ++ show f
              , formulae    = res_ty_formulae
              }
    | (f,e) <- flattenBinds binds
    ]

-- | Make axioms expressing how the domain for a data type looks like
--
--   These axioms looks like
--
--   @
--     ! [U] : (U = c_Nil | U = c_Cons(s_0_Cons(U),s_1_Cons(U)))
--   @
--
--   For finite types, type predicates are added with
--   TypeGuards.typeGuardFormula. The formulas will look like this:
--
--   @
--     ! [U] : type(U,f_Bool) => (U = c_True | U = c_False)
--   @
mkDomainAxioms :: [TyCon] -> [HipSpecSubtheory]
mkDomainAxioms ty_cons =
    [ let ty = dataConType dc0
          u  = setVarType x ty
          u' = qvar u
          domain_formulae =
              [ forall' [u] $ min' u' ==>
                  ors [ u' === apply k [proj i k u' | i <- [0..arity-1] ]
                      | dc <- dcs
                      , let (k,arity) = dcIdArity dc
                      ]
--              | finiteType ty
              ]
      in  Subtheory
              { provides    = Specific (Domain ty_con)
              , depends     = []
              , description = "Domain axiom for " ++ showOutputable ty_con
              , formulae    = domain_formulae
              }
    | ty_con <- ty_cons
    , let dcs = tyConDataCons ty_con
    , dc0:_ <- [dcs]
    ]

-- | Make axioms about minrec
--
--   TODO : also try with an apartness relation
mkMinRecAxioms :: [TyCon] -> [HipSpecSubtheory]
mkMinRecAxioms ty_cons =
    [ let minrec_formulae =
              [ forall' xs $ minrec kxs ==> min' xi
              | dc <- dcs
              , let (k,arity)       = dcIdArity dc
                    xs              = take arity varNames
                    kxs             = apply k (map qvar xs)
              , i <- [0..arity-1]
              -- ^ vacuous if arity == 0
              , let xi              = qvar (xs !! i)
              ]

      in  Subtheory
              { provides    = Specific (MinRec ty_con)
              , depends     = [Specific PrimMinRec]
              , description = "minrec for " ++ showOutputable ty_con
              , formulae    = minrec_formulae
              }

    | ty_con <- ty_cons
    , let dcs = tyConDataCons ty_con
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

instance Show HipSpecExtras where
    show (Lemma s)   = "(Lemma " ++ s ++ ")"
    show (Domain tc) = "(Domain " ++ showOutputable tc ++ ")"

instance Clausifiable HipSpecExtras where
    mkClause (Lemma s) = namedClause ("Lemma{" ++ s ++ "}") lemma
    mkClause _         = clause axiom

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras

-- I once had the idea to put a specialised trimmer here, but I got
-- confused what to do about the lemmas

data Theory = Theory { subthys :: [HipSpecSubtheory] }
