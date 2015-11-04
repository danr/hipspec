-- | A hacky way of parsing the property language DSL
module HipSpec.ParseDSL where

--import Type
--import Outputable
--
import Var hiding (Id)
import HipSpec.GHC.Utils
import Data.List
import HipSpec.Id
import HipSpec.Lang.Type
import qualified HipSpec.Lang.CoreToRich as CTR
import TyCon (TyCon)

import qualified Data.Foldable as F
import Module

import Name hiding (varName)
import Data.List

import Var hiding (Id,isId)
import TyCon (TyCon)

varWithPropType :: Var -> Bool
varWithPropType x = case CTR.trPolyType (varType x) of
    Right (Forall _ t) -> isPropType t
    _                  -> False

varFromPrelude :: Var -> Bool
varFromPrelude = varInTip

nameInTip :: Name -> Bool
nameInTip = F.any (\ n -> moduleNameString (moduleName n) == "HipSpec") . nameModule_maybe

varInTip :: Var -> Bool
varInTip = nameInTip . varName

isPropTyCon :: TyCon -> Bool
isPropTyCon = isPropId . idFromTyCon

ghcName :: (String -> Bool) -> Id -> Bool
ghcName k (GHCOrigin n) = k (showOutputable n)
ghcName _ _             = False

isPropId :: Id -> Bool
isPropId (GHCOrigin n) = nameInTip n && ghcName (isInfixOf "Prop") (GHCOrigin n)
isPropId _ = False

isPropType  :: Type Id -> Bool
isPropType t =
    case res of
        TyCon p as -> isPropId p && not (any isPropType as)
        _          -> False
  where
    (_args,res) = collectArrTy t

fromPrelude :: Id -> Bool
fromPrelude = maybe False nameInTip . tryGetGHCName -- or [ghcName (isInfixOf x) i | x <- mods ]

isMain      :: Id -> Bool
isMain      = ghcName (isInfixOf "main")

isEquals    :: Id -> Bool
isEquals    = ghcName (isInfixOfs [":=:","=:="])

isGiven     :: Id -> Bool
isGiven     = ghcName (isInfixOfs ["Given","given","==>"])

isTotal     :: Id -> Bool
isTotal     = ghcName (isInfixOfs ["Total","total"])

isGivenBool :: Id -> Bool
isGivenBool = ghcName (isInfixOf "givenBool")

isProveBool :: Id -> Bool
isProveBool = ghcName (isInfixOf "proveBool")

isOops      :: Id -> Bool
isOops      = ghcName (isInfixOfs ["Oops","oops"])

isInfixOfs :: [String] -> String -> Bool
isInfixOfs ss s = any (`isInfixOf` s) ss

