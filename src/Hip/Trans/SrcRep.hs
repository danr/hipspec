module Hip.Trans.SrcRep where

import Var

import Halo.Shared

import Data.List

isPropType  :: Var -> Bool
isPropType  = isInfixOf "Prop" . showOutputable . varType

isMain      :: Var -> Bool
isMain      = isInfixOf "main" . showOutputable

isEquals    :: Var -> Bool
isEquals    = isInfixOf ":=:" . showOutputable

isProveBool :: Var -> Bool
isProveBool = isInfixOf "proveBool" . showOutputable

isOops      :: Var -> Bool
isOops      = isInfixOf "oops" . showOutputable


