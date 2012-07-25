{-# LANGUAGE RecordWildCards #-}
module Halo.FOL.Style where

import Outputable hiding (quote)

import Halo.Util

data Style q v = Style
    { linFun      :: v -> SDoc
    -- ^ Pretty printing functions and variables
    , linCtor     :: v -> SDoc
    -- ^ Pretty printing constructors
    , linSkolem   :: v -> SDoc
    -- ^ Pretty printing Skolemised variables
    , linQVar     :: q -> SDoc
    -- ^ Quantified variables
    , linApp      :: SDoc
    -- ^ The app/@ symbol
    , linMin      :: SDoc
    -- ^ The min symbol
    , linMinRec   :: SDoc
    -- ^ The minrec symbol
    , linCF       :: SDoc
    -- ^ The CF symbol
    , linProj     :: Int -> v -> SDoc
    -- ^ Projections
    , linPtr      :: v -> SDoc
    -- ^ Pointers
    , linCNF      :: Bool
    -- ^ Write things in cnf if possible
    , linComments :: Bool
    -- ^ Print comments
    }

data StyleConf = StyleConf
    { style_cnf        :: Bool
    , style_dollar_min :: Bool
    , style_comments   :: Bool
    }

strStyle :: StyleConf -> Style String String
strStyle StyleConf{..} = Style
    { linFun      = text . quote . ("f_" ++)
    , linCtor     = text . quote . ("c_" ++)
    , linSkolem   = text . quote . ("a_" ++)
    , linQVar     = text . (\s@(_:xs) -> if any requiresQuote xs then quote s else s)
    , linApp      = text "app"
    , linMin      = text ((style_dollar_min ? ('$':)) "min")
    , linMinRec   = text "minrec"
    , linCF       = text "cf"
    , linProj     = \i n -> text (quote ("p_" ++ show i ++ "_" ++ n))
    , linPtr      = text . quote . ("ptr_" ++)
    , linCNF      = style_cnf
    , linComments = style_comments
    }
  where
    quote s@(x:xs)
        | x `notElem` ('_':['a'..'z']) || any requiresQuote xs = "'" ++ s ++ "'"
        | otherwise = s
    quote "" = "''"

    requiresQuote = (`notElem` ('_':['0'..'9']++['a'..'z']++['A'..'Z']))
