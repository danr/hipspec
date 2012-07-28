{-# LANGUAGE RecordWildCards #-}
module Halo.FOL.Style where

import Outputable hiding (quote,underscore)

import Halo.Util
import Data.Char

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
    { linFun      = text . maybe_quote . ("f_" ++)
    , linCtor     = text . maybe_quote . ("c_" ++)
    , linSkolem   = text . maybe_quote . ("a_" ++)
    , linQVar     = text . (\s@(_:xs) -> if str_needs_quotes xs then quote s else s)
    , linApp      = text "app"
    , linMin      = text ((style_dollar_min ? ('$':)) "min")
    , linMinRec   = text "minrec"
    , linCF       = text "cf"
    , linProj     = \i n -> text (maybe_quote ("p_" ++ show i ++ "_" ++ n))
    , linPtr      = text . maybe_quote . ("ptr_" ++)
    , linCNF      = style_cnf
    , linComments = style_comments
    }
  where
    quote s = "'" ++ s ++ "'"

    maybe_quote s@(x:xs)
        | init_char_needs_quotes x || str_needs_quotes xs = "'" ++ s ++ "'"
        | otherwise = s
    maybe_quote "" = "''"

    str_needs_quotes = any char_needs_quotes

    init_char_needs_quotes c =
        let x = ord c
        in  not (underscore x || lowercase x)

    char_needs_quotes c =
        let x = ord c
        in  not (underscore x || lowercase x || uppercase x)

    underscore x = x == 95
    lowercase  x = x >= 97 && x <= 122
    uppercase  x = x >= 65 && x <= 90
