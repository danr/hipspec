module Halt.FOL.Style where

import Outputable

import Halt.FOL.Linearise

strStyle :: Bool -> Style String String
strStyle cnf = Style
    { linFun  = text
    , linCtor = text
    , linQVar = text
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i n -> text (n ++ "_" ++ show i)
    -- ^ Possible collision here...
    , linPtr  = text . ("ptr" ++)
    , linCNF  = cnf
    , linConstant = text . show
    , linComments = True
    }

