module Halo.FOL.Style where

import Outputable

import Halo.FOL.Linearise

strStyle :: Bool -> Style String String
strStyle cnf = Style
    { linFun  = text
    , linCtor = text
    , linQVar = text
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i n -> text ("p_" ++ show i ++ "_" ++ n)
       -- Possible collision here...
    , linPtr  = text . ("ptr" ++)
    , linCNF  = cnf
    , linConstant = text . show
    , linComments = True
    }

