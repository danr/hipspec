{-# LANGUAGE PatternGuards #-}
module FreeTyCons (bindsTyCons) where

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

-- | Is this Id a data or newtype constructor?
--
--   Note: cannot run isDataConWorkId on things that aren't isId,
--         then we get a panic from idDetails.
isDataConId :: Id -> Bool
isDataConId v = isId v && (isConLikeId v || isNewtypeConId v)

-- | Is this Id a "constructor" to a newtype?
isNewtypeConId :: Id -> Bool
isNewtypeConId i
    | Just dc <- isDataConId_maybe i = isNewTyCon (dataConTyCon dc)
    | otherwise = False

bindsTyCons :: [CoreBind] -> [TyCon]
bindsTyCons = S.toList . S.unions . map bindTyCons

bindTyCons :: CoreBind -> Set TyCon
bindTyCons = S.unions . map exprTyCons . rhssOfBind

-- | For all used constructors in expressions and patterns,
--   return the TyCons they originate from
exprTyCons :: CoreExpr -> Set TyCon
exprTyCons e =
    let safeIdDataCon c = guard (isId c) >> isDataConId_maybe c

        as_exprs = S.fromList
                 . mapMaybe safeIdDataCon . varSetElems
                 . exprSomeFreeVars isDataConId $ e

        in_patterns = patCons e

    in  S.map dataConTyCon (as_exprs `S.union` in_patterns)

-- | Returs the constructors used in patterns
patCons :: CoreExpr -> Set DataCon
patCons e0 = case e0 of
    Case e _ _ alts -> S.unions (patCons e:map patConsAlt alts)
    App e1 e2  -> patCons e1 `S.union` patCons e2
    Let bs e   -> S.unions (patCons e:map patCons (rhssOfBind bs))
    Lam _ e    -> patCons e
    Cast e _   -> patCons e
    Tick _ e   -> patCons e
    Var{}      -> S.empty
    Lit{}      -> S.empty
    Type{}     -> S.empty
    Coercion{} -> S.empty

patConsAlt :: CoreAlt -> Set DataCon
patConsAlt (alt,_,rhs) = patConsPat alt `S.union` patCons rhs

patConsPat :: AltCon -> Set DataCon
patConsPat p = case p of
    DataAlt c -> S.singleton c
    LitAlt{}  -> S.empty
    DEFAULT   -> S.empty

