{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
-- Translating data types

module Halt.Data where

import DataCon
import Id
import Name
import TyCon

import Halt.FOL.Abstract

import Halt.PrimCon


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

-- | Makes projection/injectivity axioms
--   TODO : Fix this code copy with mkDiscrim and translate.arities
--          and with trCase.
mkProjs :: [TyCon] -> [AxClause]
mkProjs ty_cons = do
   DataTyCon cons _ <- map algTyConRhs ty_cons
   c <- cons
   let data_con        = dataConWorkId c
       (_,_,ty_args,_) = dataConSig c
       arity           = length ty_args
   i <- [0..arity-1]

   let names  = take arity varNames
       unproj = fun data_con (map qvar names)

   return $ Clause Axiom "proj" $
              forall' names $
                min' unproj ==> proj i data_con unproj === qvar (names !! i)

-- | Make discrimination axioms
mkDiscrim :: [TyCon] -> [AxClause]
mkDiscrim ty_cons = do
   DataTyCon cons _ <- map algTyConRhs ty_cons
   let allcons = map ((,) True) cons ++ map ((,) False) [primCon BAD,primCon UNR]
   (c,unequals) <- zip cons (drop 1 $ tails allcons)
   (need_min,uneq_c) <- unequals
   let data_c          = dataConWorkId c
       (_,_,ty_args,_) = dataConSig c
       arity           = length ty_args

       uneq_data_c          = dataConWorkId uneq_c
       (_,_,uneq_ty_args,_) = dataConSig uneq_c
       uneq_arity           = length uneq_ty_args

       names      = take arity varNames
       uneq_names = take uneq_arity (drop arity varNames)

       lhs    = fun data_c (map qvar names)
       rhs    = fun uneq_data_c (map qvar uneq_names)

   return $ Clause Axiom "discrim" $
              forall' (names ++ uneq_names) $
                 ([min' lhs] ++ [ min' rhs | need_min ]) ===> lhs =/= rhs

-- | Make axioms about CF
mkCF :: [TyCon] -> [AxClause]
mkCF ty_cons = concat $ do
    DataTyCon cons _ <- map algTyConRhs ty_cons
    c <- cons
    let data_c          = dataConWorkId c
        (_,_,ty_args,_) = dataConSig c
        arity           = length ty_args
        vars            = take arity varNames
        xbar            = map qvar vars
        kxbar           = fun data_c xbar

    return $
      (Clause Axiom "assemblecf" $ forall' vars $
          min' kxbar : map cf xbar ===> cf kxbar)
      :
      (guard (arity > 0) >>
         [ Clause Axiom "disassemblecf" $ forall' vars $
             cf kxbar ==> ands (map cf xbar)


         , Clause Axiom "disassemblencf" $ forall' vars $
              [ min' kxbar , neg (cf kxbar) ] ===>
                   ors [ min' x /\ neg (cf x) | x <- xbar ]
         ])

axiomsBadUNR :: [AxClause]
axiomsBadUNR =
    [ Clause Axiom "cfunr"  $ cf (fun0 (primId UNR))
    , Clause Axiom "ncfbad" $ neg (cf (fun0 (primId BAD)))
    , Clause Axiom "minbad" $ min' (fun0 (primId BAD))
    , Clause Axiom "cfmin"  $ forall' [x] (cf (qvar x) ==> min' (qvar x))
    ]
  where
    x = head varNames

-- | A bunch of variable names to quantify over
varNames :: [Int]
varNames = [0..]
