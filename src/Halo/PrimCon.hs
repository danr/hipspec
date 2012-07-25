{-# LANGUAGE DeriveDataTypeable #-}
module Halo.PrimCon where

import CoreSyn
import DataCon
import Id
import Name
import SrcLoc
import Unique
import Data.Data
import TysWiredIn

import Halo.FOL.Abstract

data PrimCon = BAD | UNR deriving (Show,Eq,Ord,Enum,Bounded,Data,Typeable)

true,false,unr,bad :: Term'
true  = con trueDataConId
false = con falseDataConId
unr   = con (primId UNR)
bad   = con (primId BAD)

primName :: PrimCon -> Name
primName c = mkInternalName
    (mkUnique 'j' (fromEnum c))
    (mkOccName dataName (show c))
    wiredInSrcSpan

primId :: PrimCon -> Id
primId c = mkVanillaGlobal (primName c) ty_err
  where ty_err = error $ "primId: type on " ++ show c

primExpr :: PrimCon -> CoreExpr
primExpr = Var . primId

primCon :: PrimCon -> DataCon
primCon c = mkDataCon
    (primName c)
    False -- infix
    []    -- strictness
    []    -- records
    []    -- univ.q. ty vars
    []    -- ext.q. ty vars
    []    -- gadt equalities
    []    -- theta types
    []    -- argument types
    (error $ "primCon: result type (Type) on " ++ show c)
    (error $ "primCon: repr type constructor (TyCon) on" ++ show c)
    []    -- stupid theta types
    (DCIds Nothing (primId c))
