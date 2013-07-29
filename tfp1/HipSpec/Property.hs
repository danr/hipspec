-- | Properties, represented with the simple language
{-# LANGUAGE RecordWildCards, PatternGuards #-}
module HipSpec.Property
    ( Literal(..)
    , mapLiteral
    , Property(..)
    , trProperty
    , trProperties
    , tvSkolemProp
    , etaExpandProp
    ) where

import Control.Monad.Error

import Name

import Lang.Simple as S
import Lang.RichToSimple as S
import Lang.PrettyRich as R

import Text.PrettyPrint hiding (comma)

import HipSpec.ParseDSL
import HipSpec.Theory

import TysWiredIn (trueDataCon,boolTyConName)
import DataCon (dataConName)

import Data.List (intercalate)

import qualified Lang.PolyFOL as P
import qualified Lang.ToPolyFOL as P

{-# ANN module "HLint: ignore Use camelCase" #-}

data Literal = S.Expr TypedName' :=: S.Expr TypedName'

mapLiteral :: (S.Expr TypedName' -> S.Expr TypedName') -> Literal -> Literal
mapLiteral f (a :=: b) = f a :=: f b

instance Show Literal where
    show (e1 :=: e2) = showExpr e1 ++ " = " ++ showExpr e2

data Property = Property
    { prop_name     :: String
    -- ^ Name (e.g. prop_rotate)
    , prop_tvs      :: [Name']
    -- ^ Type variables
    , prop_vars     :: [TypedName']
    -- ^ Quantified variables (typed)
    , prop_goal     :: Literal
    -- ^ Goal
    , prop_assums   :: [Literal]
    -- ^ Assumptions
    , prop_repr     :: String
    -- ^ Representation (e.g. rotate (len xs) xs == xs)
    , prop_var_repr :: [String]
    -- ^ Representation of variables (e.g ["xs"])
    }

instance Show Property where
    show Property{..} = concatMap (++ "\n    ")
        [ "Property"
        , "{ prop_name = " ++ prop_name
        , ", prop_tvs = " ++ comma (map ppRename prop_tvs)
        , ", prop_vars = " ++ comma (map (render . R.ppTyped (text . ppRename)) prop_vars)
        , ", prop_goal = " ++ show prop_goal
        , ", prop_assums = " ++ comma (map show prop_assums)
        , ", prop_repr = " ++ prop_repr
        , ", prop_var_repr = " ++ comma prop_var_repr
        , "}"
        ]
     where
       comma = intercalate ","

data Err
    = CannotParse (S.Expr (S.Var Name))
    | NestedAssumptions (S.Expr (S.Var Name))
    | PropertyWithCase (S.Body (S.Var Name))
    | Internal String

instance Error Err where
    strMsg = Internal

instance Show Err where
    show err = case err of
        CannotParse e       -> "Cannot parse this as a property: " ++ showExpr e
        NestedAssumptions e -> "Nested assumptions: " ++ showExpr e
        PropertyWithCase b  -> "Property with a case: " ++ showBody b
        Internal s          -> s

trProperties :: [S.Function (S.Var Name)] -> Either Err [Property]
trProperties = mapM trProperty

-- | Translates a property that has been translated to a simple function earlier
trProperty :: S.Function (S.Var Name) -> Either Err Property
trProperty (S.Function (p ::: t) args b) = case b of
    Case{} -> throwError (PropertyWithCase b)
    Body e -> do

        let (tvs,_) = collectForalls t

        (assums,goal) <- parseProperty e

        let err = error "trProperty: initalize fields with initFields"

        return $ initFields Property
            { prop_name     = ppRename p
            , prop_tvs      = tvs
            , prop_vars     = args
            , prop_goal     = goal
            , prop_assums   = assums
            , prop_repr     = err
            , prop_var_repr = err
            }

initFields :: Property -> Property
initFields p@Property{..} = p
    { prop_repr     = intercalate " => " (map show (prop_assums ++ [prop_goal]))
    , prop_var_repr = map (ppRename . S.forget_type) prop_vars
    }

parseProperty :: S.Expr (S.Var Name) -> Either Err ([Literal],Literal)
parseProperty e = case collectArgs e of
    (Var (Old x ::: _) _,args)
        | isEquals x,    [l,r] <- args -> return ([],l :=: r)
        | isProveBool x, [l]   <- args -> return ([],l :=: true)
        | isGivenBool x, [l,q] <- args -> do
            (as,gl) <- parseProperty q
            return (l :=: true:as,gl)
        | isGiven x,     [p,q] <- args -> do
            (nested_as,a) <- parseProperty p
            unless (null nested_as) (throwError (NestedAssumptions e))
            (as,gl) <- parseProperty q
            return (a:as,gl)
    _ -> throwError (CannotParse e)
  where
    true = Var (Old (dataConName trueDataCon) ::: TyCon (Old boolTyConName) []) []

-- | Removes the type variables in a property, returns clauses defining the
--   sorts and content to ignore
tvSkolemProp :: Property -> (Property,[P.Clause LogicId],[Content])
tvSkolemProp p@Property{..} =
    ( p
        { prop_tvs  = []
        , prop_vars = [ v ::: ty_subst t | v ::: t <- prop_vars ]
        , prop_goal = sk_lit prop_goal
        , prop_assums = map sk_lit prop_assums
        }
    , sorts
    , ignore
    )
  where
    tvs = [ (tv,S.New [S.LetLoc tv] i) | (tv,i) <- zip prop_tvs [0..] ]

    (expr_substs,ty_substs) = unzip
        [ (exprTySubst tv tc,tc /// tv)
        | (tv,tv') <- tvs
        , let tc = S.TyCon tv' []
        ]

    sorts      = [ P.SortSig (P.Id tv') 0 | (_,tv') <- tvs       ]
    ignore     = [ Type tv'               | (_,S.Old tv') <- tvs ]

    expr_subst = foldr (.) id expr_substs
    ty_subst   = foldr (.) id ty_substs
    sk_lit     = mapLiteral expr_subst

-- | Eta-expands a property, if possible
etaExpandProp :: Property -> Property
etaExpandProp p@Property{..}
    | e :=: _ <- prop_goal
    , (ts,_res_ty) <- collectArrTy (S.exprType e)
    , not (null ts) =
        let new_vars  = [ New [LamLoc] i ::: t | (t,i) <- zip ts [0..] ]
            new_exprs = [ Var x [] | x <- new_vars ]
        in  initFields p
                { prop_vars = prop_vars ++ new_vars
                , prop_goal = mapLiteral (`S.apply` new_exprs) prop_goal
                }

etaExpandProp p = p




