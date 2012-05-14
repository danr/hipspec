{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
-- Translating data types

module Halt.Data where

import DataCon
import Id
import Name
import SrcLoc
import TyCon
import Unique

import FOL.Abstract

import Halt.Names

import Data.List
import Control.Monad.Reader

dataArities :: [TyCon] -> [(Name,Int)]
dataArities ty_cons =
    [ (con_name,arity)
    | DataTyCon cons _ <- map algTyConRhs ty_cons
    , con <- cons
    , let con_name        = idName (dataConWorkId con)
          (_,_,ty_args,_) = dataConSig con
          arity           = length ty_args
    ]

-- | Makes projection/injectivity axioms
--   TODO : Fix this code copy with mkDiscrim and translate.arities
--          and with trCase.
mkProjs :: [TyCon] -> [Clause Var]
mkProjs ty_cons = do
   DataTyCon cons _ <- map algTyConRhs ty_cons
   con <- cons
   let data_con        = dataConWorkId con
       (_,_,ty_args,_) = dataConSig con
       arity           = length ty_args
   i <- [0..arity-1]

   let names  = take arity varNames
       unproj = fun data_con (map qvar names)

   return $ Clause Axiom "p" $
              forall' names $
                minPred unproj ==> proj i data_con unproj === qvar (names !! i)

-- | Make discrimination axioms
mkDiscrim :: [TyCon] -> [Clause Var]
mkDiscrim ty_cons = do
   DataTyCon cons _ <- map algTyConRhs ty_cons
   let allcons = cons ++ [constantCon BAD,constantCon UNR]
   (con,unequals) <- zip cons (drop 1 $ tails allcons)
   uneq_con <- unequals
   let data_con        = dataConWorkId con
       (_,_,ty_args,_) = dataConSig con
       arity           = length ty_args

       uneq_data_con        = dataConWorkId uneq_con
       (_,_,uneq_ty_args,_) = dataConSig uneq_con
       uneq_arity           = length uneq_ty_args

       names      = take arity varNames
       uneq_names = take uneq_arity (drop arity varNames)

       lhs    = fun data_con (map qvar names)
       rhs    = fun uneq_data_con (map qvar uneq_names)

   return $ Clause Axiom "d" $
              forall' (names ++ uneq_names) $
                 minPred lhs \/ minPred rhs ==> lhs =/= rhs

-- | Make discrimination axioms
mkCF :: [TyCon] -> [Clause Var]
mkCF ty_cons = concat $ do
    DataTyCon cons _ <- map algTyConRhs ty_cons
    con <- cons
    let data_con        = dataConWorkId con
        (_,_,ty_args,_) = dataConSig con
        arity           = length ty_args
        vars            = take arity varNames
        xbar            = map qvar vars
        kxbar           = fun data_con xbar

    return $
      [ Clause Axiom "assemblecf" $ forall' vars $
          minPred kxbar : map cfPred xbar ===> cfPred kxbar

      , Clause Axiom "assemblencf" $ forall' vars $
          minPred kxbar : map (neg . cfPred) xbar ===> neg (cfPred kxbar)
      ]

      ++

      (guard (arity > 0) >>
         [ Clause Axiom "disassemblecf" $ forall' vars $
             cfPred kxbar ==> ands (map cfPred xbar)


         , Clause Axiom "disassemblencf" $ forall' vars $
              [ minPred kxbar , neg (cfPred kxbar) ] ===>
                   ors [ minPred x /\ neg (cfPred x) | x <- xbar ]
         ])

axiomsBadUNR :: [Clause Var]
axiomsBadUNR =
    [ Clause Axiom "cfunr"  $ cfPred (con (constantId UNR))
    , Clause Axiom "ncfbad" $ neg (cfPred (con (constantId BAD)))
    , Clause Axiom "minbad" $ minPred (con (constantId BAD))
    , Clause Axiom "cfmin"  $ forall' [x] (cfPred (qvar x) ==> minPred (qvar x))
    ]
  where
    x = head varNames

-- | A bunch of variable names to quantify over
varNames :: [Var]
varNames =
   [ mkVanillaGlobal
       (mkInternalName (mkUnique 'z' i) (mkOccName varName n) wiredInSrcSpan)
       (error "varNames: type")
   | i <- [0..]
   | n <- [1..] >>= flip replicateM "xyzwvu"
   ]

