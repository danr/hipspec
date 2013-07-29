{-# LANGUAGE PatternGuards #-}
module Lang.FreeTyCons (bindsTyCons,exprsTyCons) where

import CoreSyn
import CoreUtils (exprType)
import DataCon
import TyCon
import Id
import Type
import Var

import Data.Set (Set)
import qualified Data.Set as S

exprsTyCons :: [CoreExpr] -> [TyCon]
exprsTyCons = S.toList . S.unions . map exprTyCons

bindsTyCons :: [CoreBind] -> [TyCon]
bindsTyCons = S.toList . S.unions . map bindTyCons

bindTyCons :: CoreBind -> Set TyCon
bindTyCons = S.unions . map exprTyCons . rhssOfBind

tyTyCons :: Type -> Set TyCon
tyTyCons = go . expandTypeSynonyms
  where
    go t0
        | Just (t1,t2) <- splitFunTy_maybe t0    = S.union (go t1) (go t2)
        | Just (tc,ts) <- splitTyConApp_maybe t0 = S.insert tc (S.unions (map go ts))
        | Just (_,t) <- splitForAllTy_maybe t0   = go t
        | otherwise                              = S.empty

varTyCons :: Var -> Set TyCon
varTyCons = tyTyCons . varType

-- | For all used constructors in expressions and patterns,
--   return the TyCons they originate from
exprTyCons :: CoreExpr -> Set TyCon
exprTyCons e0 = case e0 of
    Case e x t alts -> S.unions (varTyCons x:tyTyCons t:exprTyCons e:map altTyCons alts)
    App e1 e2       -> S.union (exprTyCons e1) (exprTyCons e2)
    Let bs e        -> S.unions (exprTyCons e:map exprTyCons (rhssOfBind bs))
    Lam _ e         -> exprTyCons e
    Cast e _        -> exprTyCons e
    Tick _ e        -> exprTyCons e
    Var x           -> varTyCons x
    Type t          -> tyTyCons t
    Coercion{}      -> S.empty
    Lit{}           -> tyTyCons (exprType e0)

altTyCons :: CoreAlt -> Set TyCon
altTyCons (alt,_,rhs) = patTyCons alt `S.union` exprTyCons rhs

patTyCons :: AltCon -> Set TyCon
patTyCons p = case p of
    DataAlt c -> S.singleton (dataConTyCon c)
    LitAlt{}  -> S.empty
    DEFAULT   -> S.empty

