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

dataArities :: [TyCon] -> [(Name,Int)]
dataArities ty_cons =
    [ (con_name,arity)
    | DataTyCon cons _ <- map algTyConRhs ty_cons
    , c <- cons
    , let con_name        = idName (dataConWorkId c)
          (_,_,ty_args,_) = dataConSig c
          arity           = length ty_args
    ]

mkProjDiscrim :: HaloConf -> [TyCon] -> [Subtheory]
mkProjDiscrim HaloConf{..} ty_cons =
   [
     -- Projections
     let projections =
           [ forall' names $ [ min' unproj | use_min ]
                             ===> proj i data_c unproj === qvar (names !! i)
           | c <- cons
           , let data_c          = dataConWorkId c
                 (_,_,ty_args,_) = dataConSig c
                 arity           = length ty_args
                 names           = take arity varNames
                 unproj          = apply data_c (map qvar names)
           , i <- [0..arity-1]
           ]

     -- Discriminations

         discrims =
           [ forall' (names ++ uneq_names) $
                     ([min' lhs | use_min ] ++ [ min' rhs | need_min && use_min ])
                     ===> lhs =/= rhs
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
                  , depends     = [ CrashFree ty_con | use_cf ]
                  -- ^ I think we might want to make this depend on
                  --   datatypes this is defined in terms of
                  , description = showSDoc (pprSourceTyCon ty_con)
                  , formulae    = projections ++ discrims }

   | ty_con <- ty_cons
   , let DataTyCon cons _ = algTyConRhs ty_con
   ]

-- | Make axioms about CF
mkCF :: HaloConf -> [TyCon] -> [Subtheory]
mkCF HaloConf{..} ty_cons = do
    ty_con <- ty_cons
    let DataTyCon cons _ = algTyConRhs ty_con

    return $ Subtheory
        { provides    = CrashFree ty_con
        , depends     = []
        , description = "CF " ++ showSDoc (pprSourceTyCon ty_con)
        , formulae    = concat $
            [ (forall' vars ([ min' kxbar | use_min ] ++ map cf xbar ===> cf kxbar) :)
            $ guard (arity > 0) >>
              [ forall' vars $ cf kxbar ==> ands (map cf xbar)
              , forall' vars $ [ min' kxbar | use_min ] ++ [ neg (cf kxbar) ]
                            ===> ors [ ands (neg (cf x) : [ min' x | use_min ]) | x <- xbar ]
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

-- | Make pointers to constructors
mkConPtrs :: HaloConf -> [TyCon] -> [Subtheory]
mkConPtrs halo_conf ty_cons = do
    ty_con <- ty_cons
    let DataTyCon cons _ = algTyConRhs ty_con

    c <- cons
    let data_c          = dataConWorkId c
        (_,_,ty_args,_) = dataConSig c
        arity           = length ty_args
        vars            = take arity varNames

    guard (arity > 0)

    return $ (mkPtr halo_conf data_c vars) { depends = [Data ty_con] }

axiomsBadUNR :: HaloConf -> Subtheory
axiomsBadUNR HaloConf{..} = Subtheory
    { provides    = PrimConAxioms
    , depends     = []
    , description = "Axioms for BAD and UNR"
    , formulae    = fs
    }
  where
    x = head varNames
    x' = qvar x
    fs =    [ cf (constant UNR)       ]
         ++ [ neg (cf (constant BAD)) ]
         ++ [ constant UNR =/= constant BAD ]
         ++ [ forall' [x] (cf x' ==> min' x') | use_min ]
         ++ [ min' (constant BAD)             | use_min ]

mkPtr :: HaloConf -> Var -> [Var] -> Subtheory
mkPtr HaloConf{use_min,ext_eq} f as = Subtheory
    { provides    = Pointer f
    , depends     = [ ExtensionalEquality | ext_eq ]
    , description = "Pointer axiom to " ++ show f
    , formulae    = let as' = map qvar as
                    in  [ forall' as $ [ min' (apps (ptr f) as') | use_min ]
                                          ===> apps (ptr f) as' === fun f as'
                        ]

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
    vs@[f,g,x] = take 3 varNames
    [f',g',x'] = map qvar vs

-- | A bunch of variable names to quantify over
varNames :: [Var]
varNames =
   [ mkVanillaGlobal
       (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
       (error "varNames: type")
   | i <- [0..]
   | n <- [1..] >>= flip replicateM "xyzwvu"
   ]
