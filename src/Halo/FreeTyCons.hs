{-# LANGUAGE PatternGuards #-}
{-

    Obtaining the used data types in an expression, both as
    constructors or in patterns.

-}
module Halo.FreeTyCons ( freeTyCons, isNewtypeConId ) where

import CoreSyn
import DataCon
import TyCon
import CoreFVs
import VarSet
import Id

import Control.Monad

import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as S

-- | Is this Id a "constructor" to a newtype?
--   This is the only way I have found to do it...
isNewtypeConId :: Id -> Bool
isNewtypeConId i
    | Just dc <- isDataConId_maybe i = isNewTyCon (dataConTyCon dc)
    | otherwise = False

-- | For all used constructors in expressions and patterns,
--   return the TyCons they originate from
--
--   Note: cannot run isDataConWorkId on things that aren't isId,
--         then we get a panic from idDetails.
freeTyCons :: CoreExpr -> [TyCon]
freeTyCons e =
    let safeIdDataCon c = guard (isId c) >> isDataConId_maybe c

        as_exprs = mapMaybe safeIdDataCon . varSetElems
                 . exprSomeFreeVars
                    (\v -> isId v && (isConLikeId v || isNewtypeConId v)) $ e

        in_patterns = S.toList (patCons e)

    in  map dataConTyCon (as_exprs ++ in_patterns)

-- | Returs the constructors used in patterns
patCons :: CoreExpr -> Set DataCon
patCons Var{}       = S.empty
patCons Lit{}       = S.empty
patCons (App e1 e2) = patCons e1 `S.union` patCons e2
patCons (Lam _ e)   = patCons e
patCons (Let bs e)  = S.unions (patCons e:map patCons (rhssOfBind bs))
patCons (Case e _ _ alts) = S.unions (patCons e:map patConsAlt alts)
  where
    patConsAlt (alt,_,rhs) = patConsPat alt `S.union` patCons rhs

    patConsPat (DataAlt c) = S.singleton c
    patConsPat LitAlt{}    = S.empty
    patConsPat DEFAULT     = S.empty
patCons (Cast e _)  = patCons e
patCons (Tick _ e)  = patCons e
patCons Type{}      = S.empty
patCons Coercion{}  = S.empty
