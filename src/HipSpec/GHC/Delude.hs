-- | De-prelude: Delude!
module HipSpec.GHC.Delude where

import Var
import Type
import Halo.Shared
import Data.List

isPropType   :: Var -> Bool
isPropType x = typeIsProp res && not (any typeIsProp args) && not (fromPrelude x)
  where
    (args,res) = splitFunTys (varType x)

typeIsProp  :: Type -> Bool
typeIsProp  = isInfixOf "HipSpec.Prelude.Prop" . showOutputable

fromPrelude :: Var -> Bool
fromPrelude = isInfixOf "HipSpec.Prelude" . showOutputable

isMain      :: Var -> Bool
isMain      = isInfixOf "main" . showOutputable

isEquals    :: Var -> Bool
isEquals    = isInfixOfs [":=:","=:="] . showOutputable

isGiven     :: Var -> Bool
isGiven     = isInfixOfs ["Given","given","==>"] . showOutputable

isTotal     :: Var -> Bool
isTotal     = isInfixOfs ["Total","total"] . showOutputable

isGivenBool :: Var -> Bool
isGivenBool = isInfixOf "givenBool" . showOutputable

isProveBool :: Var -> Bool
isProveBool = isInfixOf "proveBool" . showOutputable

isOops      :: Var -> Bool
isOops      = isInfixOfs ["Oops","oops"] . showOutputable

isInfixOfs :: [String] -> String -> Bool
isInfixOfs ss s = any (`isInfixOf` s) ss

