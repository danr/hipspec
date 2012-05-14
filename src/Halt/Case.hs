module Halt.Case where

import CoreSyn
import CoreUtils

import Halt.Monad
import Halt.Names
import Halt.Common
import Halt.Conf

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
--   The input must be a case expression!
addBottomCase :: CoreExpr -> HaltM CoreExpr
addBottomCase (Case scrutinee binder ty alts) = do
    unr_bad <- unr_and_bad <$> asks conf

    let bottom | unr_bad   = UNR
               | otherwise = Bottom

        bottomCon = constantCon bottom
        bottomVar = constantExpr bottom

         -- _|_ -> _|_
        -- Breaks the core structure by having a new data constructor
        bottomAlt :: CoreAlt
        bottomAlt = (DataAlt bottomCon, [], bottomVar)

        -- DEFAULT -> _|_
        defaultBottomAlt :: CoreAlt
        defaultBottomAlt = (DEFAULT, [], bottomVar)

        extraAlt :: [CoreAlt]
        extraAlt | unr_bad = [(DataAlt (constantCon BAD), [], constantExpr BAD)]
                 | otherwise = []
    -- Case expressions have an invariant that the default case is always first.
    return $ Case scrutinee binder ty $ case findDefault alts of
         (as,Just def) -> (DEFAULT, [], def):bottomAlt:extraAlt++as
         (as,Nothing)  -> defaultBottomAlt:extraAlt++as
addBottomCase _ = error "addBottomCase on non-case expression"


