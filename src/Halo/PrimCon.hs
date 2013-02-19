{-# LANGUAGE DeriveDataTypeable #-}
{-

    The primitives: UNR and BAD (or those two collapsed to bottom)

-}
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

unrId,badId :: Id
unrId = primId UNR
badId = primId BAD


true,false,unr,bad,bot :: Term'
true  = con trueDataConId
false = con falseDataConId
unr   = con unrId
bad   = con badId
bot   = con bottom

unrCon,badCon,botCon :: DataCon
unrCon = primCon UNR
badCon = primCon BAD
botCon = primCon UNR     -- bottom is represented as UNR

bottom :: Id
bottom = primId UNR      -- bottom is represented as UNR

unrExpr,badExpr,botExpr :: CoreExpr
unrExpr = Var unrId
badExpr = Var badId
botExpr = Var bottom

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
