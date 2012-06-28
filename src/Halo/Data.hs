{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
-- Translating data types

module Halo.Data where

import DataCon
import Id
import Name
import Outputable
import SrcLoc
import TyCon
import Type
import TysWiredIn
import Unique

import Halo.FOL.Abstract

import Halo.PrimCon
import Halo.Conf
import Halo.Subtheory

import Data.List
import Control.Monad.Reader

true,false,unr,bad :: Term'
true  = con trueDataConId
false = con falseDataConId
unr   = constant UNR
bad   = constant BAD

dataArities :: [TyCon] -> [(Var,Int)]
dataArities ty_cons =
    [ (con_id,arity)
    | DataTyCon cons _ <- map algTyConRhs ty_cons
    , c <- cons
    , let con_id          = dataConWorkId c
          (_,_,ty_args,_) = dataConSig c
          arity           = length ty_args
    ]

mkProjDiscrims :: HaloConf -> [TyCon] -> [Subtheory]
mkProjDiscrims hc ty_cons =
   [ mkProjDiscrim hc ty_con cons
   | ty_con <- ty_cons
   , let DataTyCon cons _ = algTyConRhs ty_con
   ]

mkProjDiscrim :: HaloConf -> TyCon -> [DataCon] -> Subtheory
mkProjDiscrim HaloConf{..} ty_con cons
    | ty_con == boolTyCon && disjoint_booleans = Subtheory
        { provides    = Data ty_con
        , depends     = [ CrashFree ty_con | use_cf ]
        , description = showSDoc (pprSourceTyCon ty_con)
        , formulae    =
            [ true =/= false ] ++
            [ tf =/= ub | tf <- [true,false], ub <- [unr,bad], unr_and_bad ]
        }
    | otherwise = Subtheory
        { provides    = Data ty_con
        , depends     = [ CrashFree ty_con | use_cf ]
        , description = showSDoc (pprSourceTyCon ty_con)
        , formulae    = projections ++ discrims
        }
  where
    -- Projections
    projections =
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

    -- Discrimination
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
            [
                [ forall' vars $ (min' kxbar:map cf xbar) ===> cf kxbar ] ++

                [ forall' vars $ [cf kxbar] ===> ands (map cf xbar) 
                  -- Perhaps also add: 
                  -- min(K xs) /\ not (cf (K xs)) ==> BigOr_i (min(x_i) /\ not (cf (x_i)) 
                  -- Maybe OK, we are only nervous about negative cf making interesting elements
                  -- because all positive cf's are min and hence maybe we might get infinite models 
                  -- through the backdoor.
                | arity > 0]

            | c <- cons
            , let data_c          = dataConWorkId c
                  (_,_,ty_args,_) = dataConSig c
                  arity           = length ty_args
                  vars            = take arity varNames
                  xbar            = map qvar vars
                  kxbar           = fun data_c xbar
            ]
        }
  where
    x = head varNames

axiomsBadUNR :: [Subtheory]
axiomsBadUNR =
    [ Subtheory
         { provides    = PrimConAxioms
         , depends     = [ PrimConApps ]
         , description = "Axioms for BAD and UNR"
         , formulae    =
              [ cf unr
              , neg (cf bad)
              , unr =/= bad
              , forall' [x] $ [ x' =/= unr, cf x'] ===> min' x'
              ]
         }         
         
    , Subtheory
         { provides    = PrimConApps
         , depends     = []
         , description = "App on BAD and UNR"
         , formulae    =
              [ forall' [x] $ app bad x' === bad
              , forall' [x] $ app unr x' === unr
              , forall' [f,x] $ min' (app f' x') ==> min' f'
              ]
         }
         -- ^ Any file that uses app, but not necessarily on a pointer,
         --   remind you, it could be app on a quantified variable,
         --   should have PrimConApps as a dependency.
         --   [contracts only]
    ]
  where
    vs@[f,g,x] = take 3 varNames
    [f',g',x'] = map qvar vs


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
        let lhs = apps (ptr f) as'
            rhs = fun f as'
        in  [forall' as $ ors [min' lhs,min' rhs] ==> lhs === rhs]
    }
  where
    as  = take arity varNames
    as' = map qvar as


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
