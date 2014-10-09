-- | Properties, represented with the simple language
--
--   TODO: Make nicer pretty printers representations
{-# LANGUAGE RecordWildCards, PatternGuards, DeriveFunctor, CPP #-}
module HipSpec.Property
    ( Literal(..)
    , Origin(..)
    , mapLiteral
    , Property(..)
    , propEquation
    , isUserStated
    , isFromQS
    , trProperty
    , trProperties
    , tvSkolemProp
    , etaExpandProp
    , varsFromCoords
    , lintProperty
    , generaliseProp
    , maybePropRepr
    , cgSortProps
    , equalsTrue
    , boolifyProperty
    ) where

import Control.Monad.Error

-- import Name

import HipSpec.Lang.Simple as S
-- import HipSpec.Lang.RichToSimple as S
-- import HipSpec.Lang.PrettyRich as R
import HipSpec.Lang.Renamer
import HipSpec.Lint

import HipSpec.Unify
import Control.Unification

-- import Text.PrettyPrint hiding (comma)

import Var (Var)

import HipSpec.ParseDSL
import HipSpec.Theory
import HipSpec.Utils
import HipSpec.Property.Repr
import HipSpec.Heuristics.CallGraph

import HipSpec.Id hiding (Derived(Case))

import TysWiredIn (trueDataCon,falseDataCon,boolTyCon)
-- import DataCon (dataConName)

import Data.List (intercalate,union)
import Data.Maybe (mapMaybe)

import Data.Void

import qualified HipSpec.Lang.PolyFOL as P
import qualified HipSpec.Lang.ToPolyFOL as P

import Data.Map (Map)
import qualified Data.Map as M

import HipSpec.Unify
import Control.Unification

literalFreeTyVars :: Literal -> [Id]
literalFreeTyVars (a :=: b) = exprFreeTyVars a `union` exprFreeTyVars b

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Literals in propreties
data Literal = S.Expr Id :=: S.Expr Id

mapLiteral :: (S.Expr Id -> S.Expr Id) -> Literal -> Literal
mapLiteral f (a :=: b) = f a :=: f b

literalGbls :: Literal -> [Id]
literalGbls (a :=: b) = exprGbls a `union` exprGbls b

instance Show Literal where
    show (e1 :=: e2) = showExpr e1 ++ " = " ++ showExpr e2

-- | Origins of properties
data Origin eq
    = Equation eq
    -- ^ A QuickSpec equation
    | UserStated
    -- ^ User-stated property
  deriving (Eq,Ord,Functor)

-- | Properties
data Property eq = Property
    { prop_name     :: String
    -- ^ Name (e.g. prop_rotate)
    , prop_id       :: Id
    -- ^ Its property id...
    , prop_origin   :: Origin eq
    -- ^ Origin of the property
    , prop_tvs      :: [Id]
    -- ^ Type variables
    , prop_vars     :: [(Id,Type Id)]
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
  deriving Functor

isUserStated :: Property eq -> Bool
isUserStated p = case prop_origin p of
    UserStated -> True
    _          -> False

isFromQS :: Property eq -> Bool
isFromQS p = case prop_origin p of
    Equation{} -> True
    _          -> False

instance Show (Origin eq) where
    show o = case o of
        Equation{} -> "equation from QuickSpec"
        UserStated -> "user stated"

instance Show (Property eq) where
    show Property{..} = concatMap (++ "\n    ")
        [ "Property"
        , "{ prop_name = " ++ prop_name
        , ", prop_origin = " ++ show prop_origin
        , ", prop_tvs = " ++ comma (map ppId prop_tvs)
        , ", prop_vars = " ++ comma (map showTyped prop_vars)
        , ", prop_goal = " ++ show prop_goal
        , ", prop_assums = " ++ comma (map show prop_assums)
        , ", prop_repr = " ++ prop_repr
        , ", prop_var_repr = " ++ comma prop_var_repr
        , "}"
        ]
     where
       comma = intercalate ","

-- TODO: remove this junk
data Err
    = CannotParse (S.Expr Id)
    | NestedAssumptions (S.Expr Id)
    | PropertyWithCase (S.Body Id)
    | Internal String

instance Error Err where
    strMsg = Internal

instance Show Err where
    show err = case err of
        CannotParse e       -> "Cannot parse this as a property: " ++ showExpr e
        NestedAssumptions e -> "Nested assumptions: " ++ showExpr e
        PropertyWithCase b  -> "Property with a case: " ++ showBody b
        Internal s          -> s

trProperties :: [S.Function Id] -> Either Err [Property Void]
trProperties = mapM trProperty

-- | Translates a property that has been translated to a simple function earlier
trProperty :: S.Function Id -> Either Err (Property Void)
trProperty (S.Function p (Forall tvs ty) args b) = case b of
    Just (c@Case{}) -> throwError (PropertyWithCase c)
    Nothing         -> error "Inconceivable, property with abstract body"
    Just (Body e)   -> do

        (assums,goal) <- parseProperty e

        let err = error "trProperty: initalize fields with initFields"

            (arg_tys,_) = collectArrTy ty

        return $ initFields Property
            { prop_name     = originalId p
            , prop_id       = p
            , prop_origin   = UserStated
            , prop_tvs      = tvs
            , prop_vars     = zip args arg_tys
            , prop_goal     = goal
            , prop_assums   = assums
            , prop_repr     = err
            , prop_var_repr = err
            }

-- | Initialises the prop_repr and prop_var_repr fields
initFields :: Property eq -> Property eq
initFields p@Property{..} = evalRenameM (disambig originalId) [] $ do
    vars' <- insertMany (map fst prop_vars)
    goal:assums <- mapM show_lit (prop_goal:prop_assums)
    return p
        { prop_var_repr = vars'
        , prop_repr     = intercalate " => " (assums ++ [goal])
        }
  where
    show_lit (e1 :=: e2) = do
            t1 <- exprRepr <$> rename (zap_expr_types e1)
            t2 <- exprRepr <$> rename (zap_expr_types e2)
            return (t1 ++ " == " ++ t2)

    zap_expr_types = S.travExprTypes (fmap (const (Derived Unknown 0)))

-- | Splits a == b to a == True ==> b == True and b == True ==> a == True
--   for boolean properties
boolifyProperty :: Property eq -> [Property eq]
boolifyProperty prop@Property{..} = case prop_goal of
  lhs :=: rhs -> case S.exprType lhs of
    TyCon tc [] | tc == idFromTyCon boolTyCon, notConstant lhs, notConstant rhs ->
      let mk a b = copyReprToName $ initFields $ prop
                     { prop_assums = equalsTrue a : prop_assums
                     , prop_goal   = equalsTrue b
                     , prop_origin = UserStated -- a bit of a lie
                     }
      in  [prop, mk lhs rhs, mk rhs lhs]
    _ -> [prop]

notConstant :: S.Expr Id -> Bool
notConstant (Gbl a _ []) = a `notElem` map idFromDataCon [trueDataCon,falseDataCon]
notConstant _            = True

copyReprToName :: Property eq -> Property eq
copyReprToName p@Property{..} = p { prop_name = prop_repr }

-- | Tries to "parse" a property in the simple expression format
parseProperty :: S.Expr Id -> Either Err ([Literal],Literal)
parseProperty e = case collectArgs e of
    (Gbl x _ _,args)
        | isEquals x,    [l,r] <- args -> return ([],l :=: r)
        | isProveBool x, [l]   <- args -> return ([],equalsTrue l)
        | isGivenBool x, [l,q] <- args -> do
            (as,gl) <- parseProperty q
            return (equalsTrue l:as,gl)
        | isGiven x,     [p,q] <- args -> do
            (nested_as,a) <- parseProperty p
            unless (null nested_as) (throwError (NestedAssumptions e))
            (as,gl) <- parseProperty q
            return (a:as,gl)
    _ -> throwError (CannotParse e)

equalsTrue :: S.Expr Id -> Literal
equalsTrue l = l :=: true
  where
    true = Gbl (idFromDataCon trueDataCon) (Forall [] (TyCon (idFromTyCon boolTyCon) [])) []

-- | Removes the type variables in a property, returns clauses defining the
--   sorts and content to ignore
tvSkolemProp :: Property eq -> (Property eq,[P.Clause LogicId LogicId],[Content])
tvSkolemProp p@Property{..} =
    ( p
        { prop_tvs  = []
        , prop_vars = [ (v,ty_subst t) | (v,t) <- prop_vars ]
        , prop_goal = sk_lit prop_goal
        , prop_assums = map sk_lit prop_assums
        }
    , sorts
    , ignore
    )
  where
    tvs = [ (tv,TvSkolem tv `Derived` i) | (tv,i) <- zip prop_tvs [0..] ]

    (expr_substs,ty_substs) = unzip
        [ (exprTySubst tv tc,tc /// tv)
        | (tv,tv') <- tvs
        , let tc = S.TyCon tv' []
        ]

    sorts      = [ P.SortSig (P.Id tv') 0 | (_,tv') <- tvs ]
    ignore     = [ Type tv'               | (_,tv') <- tvs ]

    expr_subst = foldr (.) id expr_substs
    ty_subst   = foldr (.) id ty_substs
    sk_lit     = mapLiteral expr_subst

-- | Eta-expands a property, if possible
etaExpandProp :: Property eq -> Property eq
etaExpandProp p@Property{..}
    | e :=: _ <- prop_goal
    , (ts,_res_ty) <- collectArrTy (S.exprType e)
    , not (null ts) =
        let new_vars  = [ (Derived Eta i,t) | (t,i) <- zip ts [0..] ]
            new_exprs = [ Lcl x t | (x,t) <- new_vars ]
        in  initFields p
                { prop_vars = prop_vars ++ new_vars
                , prop_goal = mapLiteral (`S.apply` new_exprs) prop_goal
                }
etaExpandProp p = p

-- | String representation of the variables at these coordinates
varsFromCoords :: Property eq -> [Int] -> [String]
varsFromCoords p cs = [ prop_var_repr p !! c | c <- cs ]

-- | Maybe the QuickSpec equation this originated from
propEquation :: Property eq -> Maybe eq
propEquation p = case prop_origin p of
    Equation eq -> Just eq
    _           -> Nothing

-- | Lint pass on a property
lintProperty :: Property eq -> Maybe String
lintProperty prop@Property{..} =
    case concatMap (lintLiteral prop_vars) (prop_goal:prop_assums) of
        []   -> Nothing
        errs -> Just (unlines (show prop:"Linting failed:":errs))

-- | Lint pass on a literal
lintLiteral :: [(Id,Type Id)] -> Literal -> [String]
lintLiteral sc lit@(e1 :=: e2) = ty_err ++ lint_errs
  where
    t1 = exprType e1
    t2 = exprType e2

    ty_err :: [String]
    ty_err
        | not (eqType t1 t2) = return $
            "Mismatching types in literal" ++
            "\n\t" ++ show lit ++
            ":\n\tlhs: " ++ showType t1 ++
            "\n\trhs: " ++ showType t2
        | otherwise = []

    lint_errs = map lint_err $ mapMaybe (lintSimpleExpr sc) [e1,e2]

    lint_err e = "Lint error in literal\n\t" ++ show lit ++ ":\n" ++ e

-- | Generalise a property
generaliseProp :: Property eq -> Property eq
generaliseProp prop@Property{..}
    = case res of
        Right (vs,goal:assums) ->
            let vars = [ (v,fmap un_u t) | (v,t) <- vs ]
                tvs  = nubSorted $
                    concatMap (freeTyVars . snd) vars ++
                    concatMap literalFreeTyVars (goal:assums)
            in  prop
                    { prop_tvs    = tvs
                    , prop_vars   = vars
                    , prop_goal   = goal
                    , prop_assums = assums
                    }
        _ -> prop
  where
    res = runGen $ do
        vi <- insertVars (map fst prop_vars)
        mk_ga <- mapM gen_lit (prop_goal:prop_assums)
        ga <- sequence mk_ga
        vs <- lookupVars vi
        return (vs,ga)

    gen_lit (e1 :=: e2) = do
        (t1,i1) <- genExpr e1
        (t2,i2) <- genExpr e2
        void (lift (unify t1 t2))
        return $ do
            e1' <- extExpr i1
            e2' <- extExpr i2
            return (fmap un_u e1' :=: fmap un_u e2')

    un_u (Fresh i) = GenTyVar `Derived` (toInteger i - toInteger (minBound :: Int))
    un_u (U a) = a

maybePropRepr :: Property eq -> Maybe String
maybePropRepr prop
    | isUserStated prop = Just (prop_repr prop)
    | otherwise         = Nothing

propertyGbls :: Property eq -> [Id]
propertyGbls = literalGbls . prop_goal

cgSortProps :: Map Var [Var] -> [Property eq] -> [Property eq]
cgSortProps callg = concat . sortByGraph callg' propertyGbls
  where
    callg' = M.fromList [ (idFromVar i,map idFromVar is) | (i,is) <- M.toList callg ]

