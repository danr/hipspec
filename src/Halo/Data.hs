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
                  , depends     = []
                  -- ^ Make this depend on datatypes this is defined in terms of
                  , description = showSDoc (pprSourceTyCon ty_con)
                  , formulae    = projections ++ discrims }

   | ty_con <- ty_cons
   , let DataTyCon cons _ = algTyConRhs ty_con
   ]

-- | Make axioms about CF
mkCF :: HaloConf -> [TyCon] -> [Subtheory]
mkCF HaloConf{..} ty_cons | use_cf = do
    ty_con <- ty_cons
    let DataTyCon cons _ = algTyConRhs ty_con
    c <- cons
    let data_c          = dataConWorkId c
        (_,_,ty_args,_) = dataConSig c
        arity           = length ty_args
        vars            = take arity varNames
        xbar            = map qvar vars
        kxbar           = fun data_c xbar

    return $ Subtheory (CrashFree ty_con) []
                       ("CF " ++ showSDoc (pprSourceTyCon ty_con))
           $ forall' vars ([ min' kxbar | use_min ] ++ map cf xbar ===> cf kxbar)
           : (guard (arity > 0) >>
                [ forall' vars $ cf kxbar ==> ands (map cf xbar)
                , forall' vars $ [ min' kxbar | use_min ] ++ [ neg (cf kxbar) ]
                                 ===> ors [ min' x /\ neg (cf x) | x <- xbar ]
                ])
mkCF _ _ = []

axiomsBadUNR :: HaloConf -> [Subtheory]
axiomsBadUNR HaloConf{..} | unr_and_bad =
    [ Subtheory { provides    = PrimConAxioms
                , depends     = []
                , description = "Axioms for BAD and UNR"
                , formulae    = fs
                } ]
  where
    x = head varNames
    fs =    [ cf (constant UNR)       | use_cf ]
         ++ [ neg (cf (constant BAD)) | use_cf  ]
         ++ [ constant UNR =/= constant BAD ]
         ++ [ forall' [x] (cf (qvar x) ==> min' (qvar x)) | use_min && use_cf ]
         ++ [ min' (constant BAD)                         | use_min ]
axiomsBadUNR _ = []

-- | A bunch of variable names to quantify over
varNames :: [Var]
varNames =
   [ mkVanillaGlobal
       (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
       (error "varNames: type")
   | i <- [0..]
   | n <- [1..] >>= flip replicateM "xyzwvu"
   ]
