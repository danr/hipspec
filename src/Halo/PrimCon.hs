{-# LANGUAGE DeriveDataTypeable #-}
module Halo.PrimCon where

import CoreSyn
import DataCon
import Data.Data
import FastString
import Id
import MkId
import Module (Module)
import Name
import PrelNames
import TypeRep
import TysPrim
import TysWiredIn
import Unique

import Halo.FOL.Abstract

data PrimCon = BAD | UNR deriving (Show,Eq,Ord,Enum,Bounded,Data,Typeable)

true,false,unr,bad :: Term'
true  = con trueDataConId
false = con falseDataConId
unr   = con (primId UNR)
bad   = con (primId BAD)

-- | Copied from TysWiredIn since it is not exported
mkWiredInDataConName :: BuiltInSyntax -> Module -> FastString -> Unique
                     -> DataCon -> Name
mkWiredInDataConName built_in modu fs unique datacon = mkWiredInName
    modu
    (mkDataOccFS fs)
    unique
    (ADataCon datacon) -- Relevant DataCon
    built_in

primName :: PrimCon -> Name
primName c = mkWiredInDataConName
    BuiltInSyntax
    gHC_TYPES
    (fsLit (show c))
    (mkUnique 'j' (fromEnum c))
    (primCon c)

primId :: PrimCon -> Id
primId = dataConWorkId . primCon

primExpr :: PrimCon -> CoreExpr
primExpr = Var . primId

primCon :: PrimCon -> DataCon
primCon c = data_con
  where
    data_con = mkDataCon
        dc_name  -- name (from primName)
        False    -- infix
        []       -- strictness
        []       -- records
        []       -- univ.q. ty vars
        []       -- ext.q. ty vars
        []       -- gadt equalities
        []       -- theta types
        []       -- argument types
        anyTy    -- result type
        anyTyCon -- representation type constructor
        []       -- stupid theta types
        (mkDataConIds bogus_wrap_name wrk_name data_con)

    dc_name  = primName c
    wrk_key  = getUnique dc_name

    wrk_occ  = mkDataConWorkerOcc (nameOccName dc_name)
    wrk_name = mkWiredInName (nameModule dc_name) wrk_occ wrk_key
			     (AnId (dataConWorkId data_con)) UserSyntax

    bogus_wrap_name = error $ "primCon: Wired-in data wrapper id for " ++ show c
