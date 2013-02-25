{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module HipSpec.Trans.Theory
    ( HipSpecExtras(..)
    , setExtraDependencies
    , mkCFAxioms
    , mkMinRecAxioms
    , mkDomainAxioms
    , mkResultTypeAxioms
    , bottomAxioms
    , HipSpecContent
    , HipSpecSubtheory
    , Theory(..)
    ) where

import Control.Monad

import CoreSyn
import Var
import Type
import TysWiredIn
import TysPrim
import TyCon
import DataCon
import Outputable
import GHC (dataConType)

import Halo.Names
import Halo.Shared
import Halo.Subtheory
import Halo.PrimCon
import Halo.Trim
import Halo.Util
import Halo.FOL.Abstract

import HipSpec.Params

import HipSpec.Trans.Property
import HipSpec.Trans.Types
import HipSpec.Trans.TypeGuards

data HipSpecExtras
    = Lemma Int
    -- ^ Lemma with a number
    | Conjecture
    -- ^ The conjecture
    | Domain TyCon
    -- ^ Domain axiom for a data type + type predicates if finite
    | ResultType Var
    -- ^ If a function f returns a finite type t, this axiom says
    --       forall x1, .., xn . isType(f(x1,..,xn),t)
    | PrimMinRec
    -- ^  Base theory about minrec
    | MinRec TyCon
    -- ^  Recursive min for a data type
    | BottomAxioms
    -- ^ Axioms about bottom
    | AppBottomAxioms
    -- ^ App on bottom
    | CF TyCon
    -- ^ Crash-Free (finite+total) for a data type
  deriving
    (Eq,Ord)

impliesOr :: Formula q v -> [Formula q v] -> Formula q v
phi `impliesOr` [] = neg phi
phi `impliesOr` xs = phi ==> ors xs

-- | Make axioms about CF
mkCFAxioms :: [TyCon] -> [HipSpecSubtheory]
mkCFAxioms ty_cons = do
    ty_con <- ty_cons
    guard (not (isNewTyCon ty_con))
    let dcs = tyConDataCons ty_con

    return $ Subtheory
        { provides    = Specific (CF ty_con)
        , depends     = []
        , description = "CF " ++ showOutputable ty_con
        , formulae    = concat $
            [
                -- cf(K xs) ==> BigAnd_i (cf (x_i))
                [ foralls $ cf kxbar ==> ands (map cf xbar')
                | not (null xbar') ] ++

                -- min(K xs) /\ not (cf (K xs))
                --    ==> BigOr_i (min(x_i) /\ not (cf (x_i))
                [ foralls $ (min' kxbar /\ neg (cf kxbar)) `impliesOr`
                                 [ ands [neg (cf y),min' y] | y <- xbar' ]
                ]

            | dc <- dcs
            , let (k,arg_types) = dcIdArgTypes dc
                  args          = zipWith setVarType varNames arg_types
                  xbar          = map qvar args
                  is_primitive  = (`eqType` intPrimTy) . varType
                  xbar'         = map qvar (filter (not . is_primitive) args)
                  kxbar         = apply k xbar
            ]
        }

bottomAxioms :: Params -> [HipSpecSubtheory]
bottomAxioms Params{..}
    | bottoms =
        [ Subtheory
            { provides    = Specific BottomAxioms
            , depends     = []
            , description = "Axioms for bottom"
            , formulae    = [ neg (cf bot) ]
            }
        , Subtheory
            { provides    = Specific AppBottomAxioms
            , depends     = []
            , description = "Axioms for app on bottom"
            , formulae    =
                [ forall' [x] $ app bot x' === bot
                , forall' [f] $ cf f' <==>
                    forall' [x] (cf x' ==> cf (app f' x'))
                ]
            }

        ]
    | otherwise = []
  where
    a <==> b = (a ==> b) /\ (b ==> a)

-- | Make data types depend on Domain axioms, and MinRec axioms if min is used.
--   Make functions depend on finite result type axioms.
setExtraDependencies :: Params -> HipSpecSubtheory -> HipSpecSubtheory
setExtraDependencies Params{..} s@(Subtheory{..}) = case provides of
    Data ty_con -> s { depends = (min ? (Specific (MinRec ty_con) :)) $
                                 (bottoms ? (Specific (CF ty_con) :)) $
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
    [ let (args_ty,res_ty)  = splitFunTys (repType' (varType f))
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
              , description = "Result type axiom for " ++ showOutputable f
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
mkDomainAxioms :: Params -> [TyCon] -> [HipSpecSubtheory]
mkDomainAxioms Params{bottoms} ty_cons =
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
    , let dcs = tyConDataCons ty_con ++ [ botCon | bottoms ]
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
    show (Lemma s)       = "(Lemma " ++ show s ++ ")"
    show (Domain tc)     = "(Domain " ++ showOutputable tc ++ ")"
    show (ResultType v)  = "(ResultType " ++ showOutputable v ++ ")"
    show PrimMinRec      = "PrimMinRec"
    show (MinRec tc)     = "(MinRec " ++ showOutputable tc ++ ")"
    show BottomAxioms    = "BottomAxioms"
    show AppBottomAxioms = "AppBottomAxioms"
    show (CF tc)         = "(CF " ++ showOutputable tc ++ ")"

instance Clausifiable HipSpecExtras where
    mkClause (Lemma n) = namedClause ("lemma_" ++ show n ++ "_") lemma
    mkClause _         = clause axiom

type HipSpecContent = Content HipSpecExtras

type HipSpecSubtheory = Subtheory HipSpecExtras


newtype Theory = Theory { subthys :: [HipSpecSubtheory] }

