module Halt.FOL.Style where

import Var
import Name
import Outputable
import Id

import Halt.FOL.Linearise

import Data.Char

stringStyle :: Style String String
stringStyle = Style
    { linVar  = text . prettyName
    , linQVar = text
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i n -> text (n ++ "_" ++ show i)
    , linPtr  = text . (++ ".ptr")
    , linCNF  = False
    , linConstant = text . show
    , linComments = True
    }

varStyle :: Style Var Var
varStyle = Style
    { linVar  = text . prettyName . lower . showSDoc . ppr . maybeLocaliseName . idName
    , linQVar = text . capInit . showSDoc . ppr . maybeLocaliseName . idName
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i -> text . prettyName . (++  "_" ++ show i) . lower . showSDoc . ppr . localiseName . idName
    , linPtr  = text . prettyName . (++ ".ptr") . showSDoc . ppr
    , linCNF  = False
    , linConstant = text . show
    , linComments = True
    }

axStyle :: Style Int Var
axStyle = Style
    { linVar  = text . prettyName . lower . showSDoc . ppr . maybeLocaliseName . idName
    , linQVar = text . ("X" ++) . show
    , linApp  = text "app"
    , linMin  = text "min"
    , linCF   = text "cf"
    , linProj = \i -> text . prettyName . (++  "_" ++ show i) . lower . showSDoc . ppr . localiseName . idName
    , linPtr  = text . prettyName . (++ ".ptr") . showSDoc . ppr
    , linCNF  = False
    , linConstant = text . show
    , linComments = True
    }

maybeLocaliseName :: Name -> Name
maybeLocaliseName n | isSystemName n = n
                    | otherwise      = localiseName n

capInit :: String -> String
capInit (x:xs) | isAlpha x = toUpper x : xs
               | otherwise = "Q" -- < this is just dumb
capInit "" = "Q"

lower :: String -> String
lower = map toLower

