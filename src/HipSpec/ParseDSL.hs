{-# LANGUAGE ViewPatterns #-}
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

varWithPropType :: Var -> Bool
varWithPropType x = case CTR.trPolyType (varType x) of
    Right (Forall _ t) -> isPropType t
    _                  -> False

varFromPrelude :: Var -> Bool
varFromPrelude = isInfixOf "HipSpec" . showOutputable . varName

isPropTyCon :: TyCon -> Bool
isPropTyCon = isPropId . idFromTyCon

ghcName :: (String -> Bool) -> Id -> Bool
ghcName k (tryGetGHCName -> Just n) = k (showOutputable n)
ghcName _ _               = False

isPropId :: Id -> Bool
isPropId = ghcName (isInfixOf "HipSpec.Prop")

isPropType  :: Type Id -> Bool
isPropType t =
    case res of
        TyCon p as -> isPropId p && not (any isPropType as)
        _          -> False
  where
    (_args,res) = collectArrTy t

fromPrelude :: Id -> Bool
fromPrelude = ghcName (isInfixOf "HipSpec")

isMain      :: Id -> Bool
isMain      = ghcName (isInfixOf "main")

isEquals    :: Id -> Bool
isEquals    = ghcName (isInfixOfs [":=:","=:="])

isNotEquals :: Id -> Bool
isNotEquals = ghcName (isInfixOfs [":/:","=/="])

isGiven     :: Id -> Bool
isGiven     = ghcName (isInfixOfs [":==>","==>"])

isOr        :: Id -> Bool
isOr        = ghcName (isInfixOfs [":|:","\\/"])

isAnd      :: Id -> Bool
isAnd       = ghcName (isInfixOfs [":&:","/\\"])

isInfixOfs :: [String] -> String -> Bool
isInfixOfs ss s = any (`isInfixOf` s) ss

