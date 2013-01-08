module HipSpec.Trans.SrcRep where

import Var

import Halo.Shared

import Data.List

isPropType  :: Var -> Bool
isPropType  = isInfixOf "Prop" . showOutputable . varType

isMain      :: Var -> Bool
isMain      = isInfixOf "main" . showOutputable

isEquals    :: Var -> Bool
isEquals    = isInfixOfs [":=:","=:="] . showOutputable

isGiven     :: Var -> Bool
isGiven     = isInfixOfs ["Given","given","==>"] . showOutputable

isGivenBool :: Var -> Bool
isGivenBool = isInfixOf "givenBool" . showOutputable

isProveBool :: Var -> Bool
isProveBool = isInfixOf "proveBool" . showOutputable

isOops      :: Var -> Bool
isOops      = isInfixOfs ["Oops","oops"] . showOutputable

isInfixOfs :: [String] -> String -> Bool
isInfixOfs ss s = any (`isInfixOf` s) ss


