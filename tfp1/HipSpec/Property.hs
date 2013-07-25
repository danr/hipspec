-- | Properties, represented with the simple language
--
--   TODO: Make nicer pretty printers representations
{-# LANGUAGE RecordWildCards, PatternGuards, DeriveFunctor #-}
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
    ) where

import Control.Monad.Error

import Name

import HipSpec.Lang.Simple as S
import HipSpec.Lang.RichToSimple as S
import HipSpec.Lang.PrettyRich as R
import HipSpec.Lint

import HipSpec.Unify
import Control.Unification

import Text.PrettyPrint hiding (comma)

import HipSpec.ParseDSL
import HipSpec.Theory
import HipSpec.Utils

import TysWiredIn (trueDataCon,boolTyConName)
import DataCon (dataConName)

import Data.List (intercalate)
import Data.Maybe (mapMaybe)

import Data.Void

import qualified HipSpec.Lang.PolyFOL as P
import qualified HipSpec.Lang.ToPolyFOL as P

{-# ANN module "HLint: ignore Use camelCase" #-}

-- | Literals in propreties
data Literal = S.Expr TypedName' :=: S.Expr TypedName'

mapLiteral :: (S.Expr TypedName' -> S.Expr TypedName') -> Literal -> Literal
mapLiteral f (a :=: b) = f a :=: f b

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
    , prop_origin   :: Origin eq
    -- ^ Origin of the property
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

trProperties :: [S.Function (S.Var Name)] -> Either Err [Property Void]
trProperties = mapM trProperty

-- | Translates a property that has been translated to a simple function earlier
trProperty :: S.Function (S.Var Name) -> Either Err (Property Void)
trProperty (S.Function (p ::: t) args b) = case b of
    Case{} -> throwError (PropertyWithCase b)
    Body e -> do

        let (tvs,_) = collectForalls t

        (assums,goal) <- parseProperty e

        let err = error "trProperty: initalize fields with initFields"

        return $ initFields Property
            { prop_name     = ppRename p
            , prop_origin   = UserStated
            , prop_tvs      = tvs
            , prop_vars     = args
            , prop_goal     = goal
            , prop_assums   = assums
            , prop_repr     = err
            , prop_var_repr = err
            }

-- | Initialises the prop_repr and prop_var_repr fields
initFields :: Property eq -> Property eq
initFields p@Property{..} = p
    { prop_var_repr = map (ppRename . S.forget_type) prop_vars
    , prop_repr = intercalate " => " (map show (prop_assums ++ [prop_goal]))
    }

-- | Tries to "parse" a property in the simple expression format
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
tvSkolemProp :: Property eq -> (Property eq,[P.Clause LogicId],[Content])
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
etaExpandProp :: Property eq -> Property eq
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
lintLiteral :: [TypedName'] -> Literal -> [String]
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
generaliseProp prop@Property{..} = case res of
    Right (vs,goal:assums) ->
        let vars        = [ v ::: fmap un_u t | (v,t) <- vs ]
            tvs         = nubSorted (concatMap (freeTyVars . typed_type) vars)
        in  prop
                { prop_tvs    = tvs
                , prop_vars   = vars
                , prop_goal   = goal
                , prop_assums = assums
                }
    _ -> prop
  where
    res = runGen $ do
        insertVars (map forget_type prop_vars)
        mk_ga <- mapM gen_lit (prop_goal:prop_assums)
        ga <- sequence mk_ga
        vs <- readVars
        return (vs,ga)

    gen_lit (e1 :=: e2) = do
        (t1,i1) <- genExpr e1
        (t2,i2) <- genExpr e2
        void (lift (unify t1 t2))
        return $ do
            e1' <- extExpr i1
            e2' <- extExpr i2
            return (fmap (fmap un_u) e1' :=: fmap (fmap un_u) e2')

    un_u (Fresh i) = New [] (toInteger i - toInteger (minBound :: Int))
    un_u (U a) = a

