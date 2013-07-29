module HipSpec.ParseDSL where

import Var
import Type
import Lang.Utils
import Data.List
import Outputable

varWithPropType   :: Var -> Bool
varWithPropType x = typeIsProp (varType x) && not (fromPrelude x)

propType :: Type -> Bool
propType ty = typeIsProp res && not (any typeIsProp args)
  where
    (_tvs,ty') = splitForAllTys ty
    (args,res) = splitFunTys ty'

typeIsProp  :: Outputable a => a -> Bool
typeIsProp  = isInfixOf "HipSpec.Prelude.Prop" . showOutputable

fromPrelude :: Outputable a => a -> Bool
fromPrelude = isInfixOf "HipSpec.Prelude" . showOutputable

isMain      :: Outputable a => a -> Bool
isMain      = isInfixOf "main" . showOutputable

isEquals    :: Outputable a => a -> Bool
isEquals    = isInfixOfs [":=:","=:="] . showOutputable

isGiven     :: Outputable a => a -> Bool
isGiven     = isInfixOfs ["Given","given","==>"] . showOutputable

isTotal     :: Outputable a => a -> Bool
isTotal     = isInfixOfs ["Total","total"] . showOutputable

isGivenBool :: Outputable a => a -> Bool
isGivenBool = isInfixOf "givenBool" . showOutputable

isProveBool :: Outputable a => a -> Bool
isProveBool = isInfixOf "proveBool" . showOutputable

isOops      :: Outputable a => a -> Bool
isOops      = isInfixOfs ["Oops","oops"] . showOutputable

isInfixOfs :: [String] -> String -> Bool
isInfixOfs ss s = any (`isInfixOf` s) ss

