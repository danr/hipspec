module Halo.Case where

import CoreSyn
import CoreUtils

import Halo.Monad
import Halo.PrimCon
import Halo.Util
import Halo.Conf

import Control.Monad.Reader

{-

  Note about the DEFAULT case and bottom. Two situations:

  1) There is a DEFAULT case. Add a bottom alternative:

      case e of                  case e of
        DEFAULT -> e0              DEFAULT -> e0
        K1 a    -> e1      =>      K1 a    -> e1
        K2 a b  -> e2              K2 a b  -> e2
                                   Bottom  -> Bottom

  2) No DEFAULT case. Add such a case to Bottom.

      case e of                  case e of
        K1 a    -> e1              DEFAULT -> Bottom
        K2 a b  -> e2      =>      K1 a    -> e1
                                   K2 a b  -> e2


  The situation with BAD/UNR is similar. We always add a case
  BAD -> BAD, and UNR behaves just as Bottom above.

-}
-- | Adds a bottom case as described above.
addBottomCase :: [CoreAlt] -> HaloM [CoreAlt]
addBottomCase alts = do
    unr_bad <- unr_and_bad <$> asks conf

    -- unr_bad should really be trinary,
    -- ie, unr&bad, bottom, or nothing
    -- but right now not unr_bad means nothing
    -- and the code below is how you would do it for only bottom

    if unr_bad then do
            let bottomCon = primCon UNR
                bottomVar = primExpr UNR

                -- _|_ -> _|_
                -- Breaks the core structure by having a new data constructor
                bottomAlt :: CoreAlt
                bottomAlt = (DataAlt bottomCon, [], bottomVar)

                -- DEFAULT -> _|_
                defaultBottomAlt :: CoreAlt
                defaultBottomAlt = (DEFAULT, [], bottomVar)

                extraAlt :: [CoreAlt]
                extraAlt | unr_bad = [(DataAlt (primCon BAD), [], primExpr BAD)]
                         | otherwise = []

            -- Case expressions have the invariant that the default case is always first.
            return $ case findDefault alts of
                 (as,Just def) -> (DEFAULT, [], def):bottomAlt:extraAlt++as
                 (as,Nothing)  -> defaultBottomAlt:extraAlt++as

        else
            return alts
