{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
-- Translating data types

module Halo.Data where

import DataCon
import Id
import Name
import TyCon
import SrcLoc
import Outputable
import Type
import Unique

import Halo.FOL.Abstract

import Halo.PrimCon
import Halo.Conf
import Halo.Subtheory

import Data.List
import Control.Monad.Reader

dataArities :: [TyCon] -> [(Var,Int)]
dataArities ty_cons =
    [ (con_id,arity)
    | DataTyCon cons _ <- map algTyConRhs ty_cons
    , c <- cons
    , let con_id          = dataConWorkId c
          (_,_,ty_args,_) = dataConSig c
          arity           = length ty_args
    ]

mkMinRec :: [TyCon] -> [Subtheory]
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
              { provides    = MinRec ty_con
              , depends     = [PrimMinRec]
              , description = "minrec for " ++ showSDoc (pprSourceTyCon ty_con)
              , formulae    = minrec_formulae
              }

    | ty_con <- ty_cons
    , let DataTyCon cons _ = algTyConRhs ty_con
    ]
      ++
    [ Subtheory
         { provides    = PrimMinRec
         , depends     = []
         , description = "minrec implies min, and minrec on app"
         , formulae    =
                [ forall' [x]   $ minrec x' ==> min' x'
                , forall' [f,x] $ minrec (app f' x') ==> min' f'
                , forall' [f,x] $ minrec (app f' x') ==> min' x'
                ]
         }
    ]


mkProjDiscrim :: HaloConf -> [TyCon] -> [Subtheory]
mkProjDiscrim HaloConf{..} ty_cons =
   [ -- Projections
     let projections =
            [ forall' xs $ [min' kxs,min' xi] ===> proj i k kxs === xi
            | c <- cons
            , let k               = dataConWorkId c
                  (_,_,ty_args,_) = dataConSig c
                  arity           = length ty_args
                  xs              = take arity varNames
                  kxs             = apply k (map qvar xs)
            , i <- [0..arity-1]
            , let xi              = qvar (xs !! i)
            ]

     -- Discriminations

         discrims =
            [ forall' (names ++ uneq_names) $
                      min' lhs : [ min' rhs | need_min ] ===> lhs =/= rhs
            | let allcons = map ((,) True) cons
                            ++ concat [ map ((,) False) [primCon BAD,primCon UNR]
                                      | unr_and_bad ]
            , (c,unequals) <- zip cons (drop 1 $ tails allcons)
            , (need_min,uneq_c) <- unequals
            , let data_c          = dataConWorkId c
                  (_,_,ty_args,_) = dataConSig c
                  arity           = length ty_args

                  uneq_data_c          = dataConWorkId uneq_c
                  (_,_,uneq_ty_args,_) = dataConSig uneq_c
                  uneq_arity           = length uneq_ty_args

                  names      = take arity varNames
                  uneq_names = take uneq_arity (drop arity varNames)

                  lhs    = apply data_c (map qvar names)
                  rhs    = apply uneq_data_c (map qvar uneq_names)
            ]

     in Subtheory { provides    = Data ty_con
                  , depends     = [ CrashFree ty_con | use_cf ] ++
                                  [ MinRec ty_con | use_minrec ]
                  , description = showSDoc (pprSourceTyCon ty_con)
                  , formulae    = projections ++ discrims }

   | ty_con <- ty_cons
   , let DataTyCon cons _ = algTyConRhs ty_con
   ]

-- | Make axioms about CF
mkCF :: [TyCon] -> [Subtheory]
mkCF ty_cons = do
    ty_con <- ty_cons
    let DataTyCon cons _ = algTyConRhs ty_con

    return $ Subtheory
        { provides    = CrashFree ty_con
        , depends     = []
        , description = "CF " ++ showSDoc (pprSourceTyCon ty_con)
        , formulae    = concat $
            [ forall' [x] (cf (qvar x) ==> min' (qvar x)) ] :

            [
                (forall' vars (min' kxbar: map cf xbar ===> cf kxbar) :)

              $ guard (arity > 0) >>

                [ forall' vars $ cf kxbar ==> ands (map cf xbar)

                , forall' vars $ min' kxbar : [ neg (cf kxbar) ] ===>
                                     ors [ ands [neg (cf x),min' x] | x <- xbar ]
                ]
            | c <- cons
            , let data_c          = dataConWorkId c
                  (_,_,ty_args,_) = dataConSig c
                  arity           = length ty_args
                  vars            = take arity varNames
                  xbar            = map qvar vars
                  kxbar           = fun data_c xbar
            ]
        }

axiomsBadUNR :: [Subtheory]
axiomsBadUNR =
    [ Subtheory
         { provides    = PrimConAxioms
         , depends     = [ PrimConApps ]
         , description = "Axioms for BAD and UNR"
         , formulae    =
              [ cf (constant UNR)
              , neg (cf (constant BAD))
              , constant UNR =/= constant BAD
              , min' (constant BAD)
              ]
         }
    , Subtheory
         { provides    = PrimConApps
         , depends     = [ AppOnMin ]
         , description = "App on BAD and UNR"
         , formulae    =
              [ forall' [x] $ app (constant BAD) x' === constant BAD
              , forall' [x] $ app (constant UNR) x' === constant UNR
              ]
         }
         -- ^ Any file that uses app, but not necessarily on a pointer,
         --   remind you, it could be app on a quantified variable,
         --   should have PrimConApps as a dependency.
         --   [contracts only]
    ]

-- | Make pointers to constructors
mkConPtrs :: HaloConf -> [TyCon] -> [Subtheory]
mkConPtrs halo_conf ty_cons = do
    ty_con <- ty_cons
    let DataTyCon cons _ = algTyConRhs ty_con

    c <- cons
    let data_c          = dataConWorkId c
        (_,_,ty_args,_) = dataConSig c
        arity           = length ty_args

    guard (arity > 0)

    return $ (mkPtr halo_conf data_c arity) { depends = [Data ty_con] }


mkPtr :: HaloConf -> Var -> Int -> Subtheory
mkPtr HaloConf{ext_eq} f arity = Subtheory
    { provides    = Pointer f
    , depends     = [ ExtensionalEquality | ext_eq ]
    , description = "Pointer axiom to " ++ show f
    , formulae    =
        [forall' as $ min' (apps (ptr f) as') ==> apps (ptr f) as' === fun f as']

    }
  where
    as  = take arity varNames
    as' = map qvar as

appMin :: Subtheory
appMin = Subtheory
    { provides    = AppOnMin
    , depends     = []
    , description = "App on min"
    , formulae    = [forall' [f,x] $ min' (app f' x') ==> min' f']
    }

extEq :: Subtheory
extEq = Subtheory
    { provides    = ExtensionalEquality
    , depends     = []
    , description = "Extensional equality"
    , formulae    = return $
         forall' [f,g] (forall' [x] (app f' x' === app g' x') ==> f' === g')
    }
  where

-- | A bunch of variable names to quantify over
varNames :: [Var]
f,g,x :: Var
f:g:x:varNames =
    [ mkVanillaGlobal
        (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
        (error "varNames: type")
    | i <- [0..]
    | n <- ["f","g","x"] ++ ([1..] >>= flip replicateM "xyzwvu")
    ]

-- the same as terms
f',g',x' :: Term'
[f',g',x'] = map qvar [f,g,x]
