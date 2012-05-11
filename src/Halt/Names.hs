module Halt.Names
       (Names
       ,NamedConstant(..)
       ,mkNames
       ,noNames
       ,namedName
       ,namedCon
       ,namedId
       ,projFun
       ) where

import DataCon
import Id
import Name
import Outputable
import SrcLoc
import UniqSupply

import FOL.Syn

import Data.Char

import qualified Data.Map as M
import Data.Map (Map)


data NamedConstant = BAD | UNR | Bottom
  deriving (Eq,Ord,Show)

newtype Names = Names (Map NamedConstant Id)

noNames :: Names
noNames = Names M.empty

mkNames :: UniqSupply -> (Names,UniqSupply)
mkNames us = initUs us $ do
    constants <- mapM (uncurry mkConstantId)
                      [(BAD,"bad"),(UNR,"unr"),(Bottom,"bottom")]
    return (Names (M.fromList constants))

mkConstantId :: NamedConstant -> String -> UniqSM (NamedConstant,Id)
mkConstantId n s = do
    u <- getUniqueM
    let name = mkInternalName u (mkOccName dataName s) wiredInSrcSpan
        i    = mkVanillaGlobal name (error $ "mkConstantId " ++ s ++ " type")
    return (n,i)

namedName :: NamedConstant -> Names -> Name
namedName nc ns = idName (namedId nc ns)

namedId :: NamedConstant -> Names -> Id
namedId nc (Names m) = case M.lookup nc m of
    Just i  -> i
    Nothing -> error $ "namedId, could not find id for builtin " ++ show nc

namedCon :: NamedConstant -> Names -> DataCon
namedCon nc ns = mkDataCon
    (namedName nc ns)
    False -- infix
    []    -- strictness
    []    -- records
    []    -- univ.q. ty vars
    []    -- ext.q. ty vars
    []    -- gadt equalities
    []    -- theta types
    []    -- argument types
    (error $ "namedCon: result type (Type) on " ++ show nc)
    (error $ "namedCon: repr type constructor (TyCon) on" ++ show nc)
    []    -- stupid theta types
    (DCIds Nothing (namedId nc ns))

-- | Project a term
projFun :: Name -> Int -> Term -> Term
projFun con_name i t = Fun fun_name [t]
  where
    fun_name = FunName (map toLower (showSDoc (ppr (localiseName con_name))) ++ show i)

