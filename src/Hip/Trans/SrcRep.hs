module Hip.Trans.SrcRep where

import Var
import Outputable

import Data.List

isPropType  :: Var -> Bool
isPropType  = isInfixOf "Prop" . showSDoc . ppr . varType

isMain      :: Var -> Bool
isMain      = isInfixOf "main" . showSDoc . ppr

isEquals    :: Var -> Bool
isEquals    = isInfixOf "=:=" . showSDoc . ppr

isProveBool :: Var -> Bool
isProveBool = isInfixOf "proveBool" . showSDoc . ppr

