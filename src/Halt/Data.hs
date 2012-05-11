{-# LANGUAGE ParallelListComp, RecordWildCards, NamedFieldPuns #-}
-- Translating data types

module Halt.Data where

import DataCon
import Id
import Name
import TyCon

import FOL.Syn hiding ((:==))

import Halt.Common
import Halt.Conf
import Halt.Names
import Halt.Utils

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
mkProjs :: HaltConf -> [TyCon] -> [FDecl]
mkProjs HaltConf{..} ty_cons = do
   DataTyCon cons _ <- map algTyConRhs ty_cons
   con <- cons
   let data_con        = dataConWorkId con
       con_name        = idName data_con
       (_,_,ty_args,_) = dataConSig con
       arity           = length ty_args
   i <- [0..arity-1]
   let names  = map VarName (take arity varNames)
       unproj = mkFun data_con (map FVar names)
       lhs    = projFun con_name i unproj
       rhs    = FVar (names !! i)
       constr = [ minPred unproj | use_min ]
       res    = implies use_cnf constr (lhs === rhs)
       quantified | use_cnf   = res
                  | otherwise = forall' names res
   return (FDecl (if use_cnf then CNF else Axiom) "p" quantified)

-- | Make discrimination axioms
--   TODO : Remove code duplication
mkDiscrim :: HaltConf -> [TyCon] -> [FDecl]
mkDiscrim HaltConf{..} ty_cons = do
   DataTyCon cons _ <- map algTyConRhs ty_cons
   let cons' = {- bottomCon : -} cons
   (con,unequals) <- withPrevious cons'
   uneq_con <- unequals
   let data_con        = dataConWorkId con
       (_,_,ty_args,_) = dataConSig con
       arity           = length ty_args

       uneq_data_con        = dataConWorkId uneq_con
       (_,_,uneq_ty_args,_) = dataConSig uneq_con
       uneq_arity           = length uneq_ty_args

       names      = map VarName (take arity varNames)
       uneq_names = map VarName (take uneq_arity (drop arity varNames))


       lhs    = mkFun data_con (map FVar names)
       rhs    = mkFun uneq_data_con (map FVar uneq_names)

       minvar = FVar (VarName "C")

   return $ case (use_cnf,use_min) of
      (True,True)   -> FDecl CNF "d" (Neg (minPred minvar) \/ minvar != lhs \/ minvar != rhs)
      (True,False)  -> FDecl CNF "d" (lhs != rhs)
      (False,True)  -> FDecl Axiom "d" (forall' (names ++ uneq_names)
                                          (minPred lhs \/ minPred rhs ==> lhs != rhs))
      (False,False) -> FDecl Axiom "d" (forall' (names ++ uneq_names) (lhs != rhs))

varNames :: [String]
varNames = [1..] >>= flip replicateM "XYZWVU"


