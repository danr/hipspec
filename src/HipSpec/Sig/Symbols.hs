-- | Makes a symbol mapping to simple variables, types and expressions.
--
-- * Translates the variables' types once and for all
--
-- * Figures out what types functions and constructors has been applied on
{-# LANGUAGE ViewPatterns,ScopedTypeVariables,PatternGuards,RecordWildCards #-}
module HipSpec.Sig.Symbols
    ( makeSymbolMap
    , SymbolMap(..)
    , lookupCon
    , lookupVar
    , translateId
    ) where

import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Term hiding (Var,symbols,size,Expr)
import qualified Test.QuickSpec.Utils.Typeable as Ty

import HipSpec.Lang.CoreToRich
import qualified HipSpec.Lang.Rich as R
import HipSpec.Lang.Simple

import HipSpec.Theory

import HipSpec.Sig.Resolve

import HipSpec.Id

import Control.Monad

import Var hiding (Id)

import Data.List (intercalate)

import Data.Map (Map)
import qualified Data.Map as M


makeSymbolMap :: ResolveMap -> Sig -> SymbolMap
makeSymbolMap sm sig = SymbolMap{..}
  where
    var_mapping = M.fromList
        [ (v,(QSOrigin (name v) x,typeRepToType sm (symbolType v)))
        | (v,x) <- zip (variableSymbols sig) [0..]
        ]

    con_mapping = M.fromList
        [ (c,translateCon sm c (lookupSym sm c))
        | c <- constantSymbols sig
        ]

data SymbolMap = SymbolMap
    { var_mapping :: Map Symbol (Id,Type Id)
    , con_mapping :: Map Symbol (Id,PolyType Id,[Type Id])
    }

instance Show SymbolMap where
    show SymbolMap{..} = unlines $
        [ "Variable symbols" ] ++
        [ "  " ++ show s ++ " -> " ++ showTyped (v,t)
        | (s,(v,t)) <- M.toList var_mapping
        ] ++
        [ "Constant symbols" ] ++
        [ "  " ++ show s ++ " -> (" ++ ppId f ++ " :: " ++ showPolyType t ++ ") "
                            ++ intercalate "," [ "@ " ++ showType t' | t' <- ts ]
        | (s,(f,t,ts)) <- M.toList con_mapping
        ]

lookupSymb :: forall a . Map Symbol a -> Symbol -> a
lookupSymb m s = case M.lookup s m of
    Just a  -> a
    Nothing -> error $
        "HipSpec.Sig.Symbols.lookup_sym: cannot find symbol " ++ show s ++ debugStr

lookupCon :: SymbolMap -> Symbol -> Expr Id
lookupCon rm s = Gbl v t ts
  where (v,t,ts) = lookupSymb (con_mapping rm) s

lookupVar :: SymbolMap -> Symbol -> (Id,Type Id)
lookupVar = lookupSymb . var_mapping

typeRepToType :: ResolveMap -> Ty.TypeRep -> Type Id
typeRepToType sm = go
  where
    go t | Just (ta,tb) <- splitArrow t = ArrTy (go ta) (go tb)
    go t = TyCon (idFromTyCon (lookupTyCon sm ty_con)) (map go ts)
      where (ty_con,ts) = Ty.splitTyConApp t

translateCon :: ResolveMap -> Symbol -> Var -> (Id,PolyType Id,[Type Id])
translateCon sm s = translateId (typeRepToType sm (symbolType s))

translateId :: Type Id -> Var -> (Id,PolyType Id,[Type Id])
translateId t_var v = case runTM (trVar v) of -- NOTE: trVar removes the context!
    Right (R.Gbl x t_orig []) -> case m_unif of
        Just unif -> (x,t_orig,unif)
        Nothing   -> error $ "Cannot unify the two types " ++
            showPolyType t_orig ++ " and " ++ showType t_var
      where
        m_unif = unify t_orig t_var
    Right _ -> error "Not a global variable!"
    Left e -> error (show e)

unify :: Eq a => PolyType a -> Type a -> Maybe [Type a]
unify (Forall tvs t) t' = sequence [ findTv tv t t' | tv <- tvs ]

findTv :: Eq a => a -> Type a -> Type a -> Maybe (Type a)
findTv x = go
  where
    go t t' = case (t,t') of
        (TyVar y    ,_)           | x == y -> return t'
        (ArrTy t1 t2,ArrTy s1 s2)          -> go t1 s1 `mplus` go t2 s2
        (TyCon a ts ,TyCon b ss)  | a == b -> msum (zipWith go ts ss)
        _                                  -> mzero

