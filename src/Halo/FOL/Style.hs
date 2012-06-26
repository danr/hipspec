module Halo.FOL.Style where

import Outputable

import Halo.PrimCon

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
    , linConstant :: PrimCon -> SDoc
    -- ^ Constants
    , linCNF      :: Bool
    -- ^ Write things in cnf if possible
    , linComments :: Bool
    -- ^ Print comments
    }

strStyle :: Bool -> Bool -> Style String String
strStyle comments cnf = Style
    { linFun      = text . quote . ("f_" ++)
    , linCtor     = text . quote . ("c_" ++)
    , linSkolem   = text . quote . ("a_" ++)
    , linQVar     = text
    , linApp      = text "app"
    , linMin      = text "min"
    , linMinRec   = text "minrec"
    , linCF       = text "cf"
    , linProj     = \i n -> text ("p_" ++ show i ++ "_" ++ n)
    , linPtr      = text . quote . ("ptr_" ++)
    , linCNF      = cnf
    , linConstant = text . quote . ("c_" ++) . show
    , linComments = comments
    }
  where
    quote s@(x:xs)
        | x `notElem` ('_'++['a'..'z]) || any requiresQuote xs = "'" ++ c:s ++ "'"
        | otherwise = s

    requiresQuote = (`notElem` ('_':['0'..'9']++['a'..'z']++['A'..'Z']))
