module Halo.FOL.Style where

import Outputable

import Halo.PrimCon

data Style q v = Style
    { linFun   :: v -> SDoc
    -- ^ Pretty printing functions and variables
    , linCtor   :: v -> SDoc
    -- ^ Pretty printing constructors
    , linQVar  :: q -> SDoc
    -- ^ Quantified variables
    , linApp   :: SDoc
    -- ^ The app/@ symbol
    , linMin   :: SDoc
    -- ^ The min symbol
    , linCF    :: SDoc
    -- ^ The CF symbol
    , linProj  :: Int -> v -> SDoc
    -- ^ Projections
    , linPtr   :: v -> SDoc
    -- ^ Pointers
    , linConstant :: PrimCon -> SDoc
    -- ^ Constants
    , linCNF   :: Bool
    -- ^ Write things in cnf if possible
    , linComments :: Bool
    -- ^ Print comments
    }

strStyle :: Bool -> Bool -> Style String String
strStyle comments cnf = Style
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
    , linComments = comments
    }

