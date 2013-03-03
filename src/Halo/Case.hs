{-# LANGUAGE RecordWildCards #-}
{-

    Adds alternatives to UNR and BAD in cases.

    1) There is a DEFAULT branch. Add a UNR and BAD alternative:

        case e of                  case e of
          DEFAULT -> e0              DEFAULT -> e0
          K1 a    -> e1      =>      K1 a    -> e1
          K2 a b  -> e2              K2 a b  -> e2
                                     UNR     -> UNR
                                     BAD     -> BAD

    2) No DEFAULT branch. Add such a case to UNR, and one BAD -> BAD:

        case e of                  case e of
          K1 a    -> e1              DEFAULT -> UNR
          K2 a b  -> e2      =>      K1 a    -> e1
                                     K2 a b  -> e2
                                     BAD     -> BAD

    It turns out that 1) is unsound with finitely many constructors
    (which all types but Integer have), so the DEFAULT cases are
    removed by Halo.RemoveDefault

-}
module Halo.Case where

import CoreSyn
import CoreUtils

import Halo.Monad
import Halo.PrimCon
import Halo.Conf


import Control.Monad.Reader

-- | Adds alts to BAD and UNR as described above
addBottomCase :: [CoreAlt] -> HaloM [CoreAlt]
addBottomCase alts = do
    HaloConf{..} <- asks conf
    return $ case () of
        ()
            | unr_and_bad && not collapse_to_bottom -> do

                let -- DEFAULT -> _|_
                    defaultUNR :: CoreAlt
                    defaultUNR = (DEFAULT, [], unrExpr)

                    -- BAD -> BAD
                    altBAD :: CoreAlt
                    altBAD = (DataAlt badCon, [], badExpr)

                    -- UNR -> UNR    <- shouldn't be used, use removeDefault
                    altUNR :: CoreAlt
                    altUNR = (DataAlt unrCon, [], unrExpr)

                case findDefault alts of
                     (as,Just def) -> (DEFAULT,[],def):altUNR:altBAD:as
                     (as,Nothing)  -> defaultUNR:altBAD:as

            | unr_and_bad && collapse_to_bottom -> do

                let -- DEFAULT -> _|_
                    defaultBottom :: CoreAlt
                    defaultBottom = (DEFAULT, [], botExpr)

                    -- _|_ -> _|_     <- shouldn't be used, use removeDefault
                    altBottom :: CoreAlt
                    altBottom = (DataAlt botCon, [], botExpr)

                case findDefault alts of
                     (as,Just def) -> (DEFAULT,[],def):altBottom:as
                     (as,Nothing)  -> defaultBottom:as

            | otherwise -> alts

