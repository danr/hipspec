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
    ) where

import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Term hiding (Var,symbols,size,Expr)
import qualified Test.QuickSpec.Utils.Typeable as Ty

import HipSpec.Lang.CoreToRich
import HipSpec.Lang.Simple
import HipSpec.Lang.RichToSimple hiding (Var)

import HipSpec.Theory

import HipSpec.Sig.Resolve

import HipSpec.GHC.Utils

import Control.Monad

import Var
import TyCon (tyConName)

import Data.List (intercalate)

import Data.Map (Map)
import qualified Data.Map as M

makeSymbolMap :: ResolveMap -> Sig -> SymbolMap
makeSymbolMap sm sig = SymbolMap{..}
  where
    var_mapping = M.fromList
        [ (v,New [] x ::: typeRepToType sm (symbolType v))
        | (v,x) <- zip (variableSymbols sig) [0..]
        ]

    con_mapping = M.fromList
        [ (c,translateCon sm c (lookupSym sm c))
        | c <- constantSymbols sig
        ]

data SymbolMap = SymbolMap
    { var_mapping :: Map Symbol (Typed Name')
    , con_mapping :: Map Symbol (TypedName',[Type Name'])
    }

instance Show SymbolMap where
    show SymbolMap{..} = unlines $
        [ "Variable symbols" ] ++
        [ "  " ++ show s ++ " -> " ++ showTyped v
        | (s,v) <- M.toList var_mapping
        ] ++
        [ "Constant symbols" ] ++
        [ "  " ++ show s ++ " -> (" ++ showTyped f ++ ") "
                            ++ intercalate "," [ "@ " ++ showType t | t <- ts ]
        | (s,(f,ts)) <- M.toList con_mapping
        ]

lookupSymb :: forall a . Map Symbol a -> Symbol -> a
lookupSymb m s = case M.lookup s m of
    Just a  -> a
    Nothing -> error $
        "HipSpec.Sig.Symbols.lookup_sym: cannot find symbol " ++ show s ++ debugStr

lookupCon :: SymbolMap -> Symbol -> Expr TypedName'
lookupCon rm s = Var v (map star ts)
  where (v,ts) = lookupSymb (con_mapping rm) s

lookupVar :: SymbolMap -> Symbol -> Typed Name'
lookupVar = lookupSymb . var_mapping

typeRepToType :: ResolveMap -> Ty.TypeRep -> Type Name'
typeRepToType sm = go
  where
    go t | Just (ta,tb) <- splitArrow t = ArrTy (go ta) (go tb)
    go t = TyCon (Old (tyConName (lookupTyCon sm ty_con))) (map go ts)
      where (ty_con,ts) = Ty.splitTyConApp t

translateCon :: ResolveMap -> Symbol -> Var -> (TypedName',[Type Name'])
translateCon sm s v = case fmap (fmap Old) (trVar v) of
    Right x@(_ ::: t_orig) -> case m_unif of
        Just unif -> (x,unif)
        Nothing   -> err $ "Cannot unify the two types " ++
            showType t_orig ++ " and " ++ showType t_sym
      where
        t_sym  = typeRepToType sm (symbolType s)

        m_unif = unify t_orig t_sym
    Left e -> err (show e)
  where
    err :: forall a . String -> a
    err str = error $
        "HipSpec.Sig.Symbols.resolveCon: " ++ str ++
        " from var " ++ showOutputable v ++
        " and symbol " ++ show s

unify :: Eq a => Type a -> Type a -> Maybe [Type a]
unify (collectForalls -> (tvs,t)) t' = sequence [ findTv tv t t' | tv <- tvs ]

findTv :: Eq a => a -> Type a -> Type a -> Maybe (Type a)
findTv x = go
  where
    go t t' = case (t,t') of
        (TyVar y    ,_)           | x == y -> return t'
        (ArrTy t1 t2,ArrTy s1 s2)          -> go t1 s1 `mplus` go t2 s2
        (TyCon a ts ,TyCon b ss)  | a == b -> msum (zipWith go ts ss)
        _                                  -> mzero

