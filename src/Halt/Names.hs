module Halt.Names where

import DataCon
import Id
import Name
import Outputable
import SrcLoc
import Unique

import FOL.Syn

import Data.Char

data NamedConstant = BAD | UNR | Bottom
  deriving (Eq,Ord,Enum)

instance Show NamedConstant where
  show BAD = "bad"
  show UNR = "unr"
  show Bottom = "bottom"

constantName :: NamedConstant -> Name
constantName c = mkInternalName (mkUnique 'j' (fromEnum c))
                                (mkOccName dataName (show c))
                                wiredInSrcSpan

constantId :: NamedConstant -> Id
constantId c = mkVanillaGlobal (constantName c) ty_err
  where ty_err = error $ "constantId: type on " ++ show c

constantCon :: NamedConstant -> DataCon
constantCon c = mkDataCon (constantName c)
                          False -- infix
                          []    -- strictness
                          []    -- records
                          []    -- univ.q. ty vars
                          []    -- ext.q. ty vars
                          []    -- gadt equalities
                          []    -- theta types
                          []    -- argument types
                          (error $ "constantCon: result type (Type) on " ++ show c)
                          (error $ "constantCon: repr type constructor (TyCon) on" ++ show c)
                          []    -- stupid theta types
                          (DCIds Nothing (constantId c))

-- | Project a term
projFun :: Name -> Int -> Term -> Term
projFun con_name i t = Fun fun_name [t]
  where
    fun_name = FunName (map toLower (showSDoc (ppr (localiseName con_name))) ++ show i)

