{-# LANGUAGE RecordWildCards,NamedFieldPuns,PatternGuards,ViewPatterns,DeriveFunctor #-}
module HipSpec.Trans.Property
    ( Literal(..)
    , Property(..)
    , Origin(..)
    , propEquation
    , propCoreExprEquation
    , isUserStated
    , isFromQS
    , varsFromCoords
    , inconsistentProperty
    , trProperty
    , totalityProperty
    ) where

import HipSpec.Trans.SrcRep
import Test.QuickSpec.Reasoning.PartialEquationalReasoning hiding
    (Total,equal)

import qualified Test.QuickSpec.Reasoning.PartialEquationalReasoning as PER

import Type
import CoreSyn
import CoreUtils (exprType)
import Var
import Id
import TysWiredIn

import Halo.Shared
import Halo.Names (varNames)

import Data.List (nub)
import Data.Function (on)
import Control.Arrow (second)

import Data.Void

data Literal
    = CoreExpr :== CoreExpr
    | Total CoreExpr

instance Show Literal where
    show (e1 :== e2) = showOutputable e1 ++ " :== " ++ showOutputable e2
    show (Total e)   = "Total(" ++ showOutputable e ++ ")"

data Origin eq
    = Equation eq
    | Totality Totality
    | UserStated
    | Builtin
  deriving (Eq,Ord,Functor)

propCoreExprEquation :: Property eq -> Maybe (CoreExpr,CoreExpr)
propCoreExprEquation (propLiteral -> e1 :== e2) = Just (e1,e2)
propCoreExprEquation _                          = Nothing

propEquation :: Property eq -> Maybe eq
propEquation (propOrigin -> Equation eq) = Just eq
propEquation _                           = Nothing

isUserStated :: Property eq -> Bool
isUserStated (propOrigin -> UserStated) = True
isUserStated _                          = False

isFromQS :: Property eq -> Bool
isFromQS (propOrigin -> Equation{}) = True
isFromQS _                          = False

data Property eq = Property
    { propLiteral    :: Literal
    , propAssume     :: [Literal]
    , propVars       :: [(Var,Type)]
    , propType       :: Type
    , propName       :: String
    , propRepr       :: String
    , propVarRepr    :: [String]
    , propOrigin     :: Origin eq
    , propOffsprings :: IO [Property eq]
    , propFunDeps    :: [Var]
    , propOops       :: Bool
    -- ^ It's an error if this property was provable
    }
  deriving Functor

instance Eq (Property eq) where
    (==) = equal propName .&&. equal (map fst . propVars)

(.&&.) :: (a -> b -> Bool) -> (a -> b -> Bool) -> a -> b -> Bool
(f .&&. g) x y = f x y && g x y

equal :: Eq b => (a -> b) -> a -> a -> Bool
equal = ((==) `on`)

varsFromCoords :: Property eq -> [Int] -> [String]
varsFromCoords p cs = [ propVarRepr p !! c | c <- cs ]

instance Show (Property eq) where
    show Property{..} = concat
        ["Property "
        ,"{ propLiteral = ", show propLiteral
        ,", propAssume = ", show propAssume
        ,", propVars = ", showOutputable propVars
        ,", propType = ", showOutputable propType
        ,", propName = ", show propName
        ,", propRepr = ", show propRepr
        ,", propFunDeps = ", showOutputable propFunDeps
        ,", propOops = ", show propOops
        ,"}"
        ]

inconsistentProperty :: Property eq
inconsistentProperty = Property
    { propLiteral    = Var trueDataConId :== Var falseDataConId
    , propAssume     = []
    , propVars       = []
    , propType       = boolTy
    , propName       = "inconsistencyCheck"
    , propRepr       = "inconsistecy check: this should never be provable"
    , propVarRepr    = []
    , propOrigin     = Builtin
    , propOffsprings = return []
    , propFunDeps    = []
    , propOops       = True
    }

-- The bool is the oops
parseProperty :: CoreExpr -> Maybe (Literal,[Literal],Bool)
parseProperty e = case second trimTyArgs (collectArgs e) of
    (Var x,[l])   | isTotal x     -> Just (Total l,[],False)
    (Var x,[l,r]) | isEquals x    -> Just (l :== r,[],False)
    (Var x,[l])   | isProveBool x -> Just (l :== Var trueDataConId,[],False)
    (Var x,[p,q]) | isGiven x     -> do
        (a,[],False) <- parseProperty p
        (u,as,o) <- parseProperty q
        return (u,a:as,o)
    (Var x,[b,q]) | isGivenBool x     -> do
        (u,as,o) <- parseProperty q
        return (u,(b :== Var trueDataConId):as,o)
    _ -> Nothing

trProperty :: CoreBind -> Maybe (Property Void)
trProperty (NonRec prop_name e) = do
    let (ty_vars,vars,e0) = collectTyAndValBinders e

    (lit,assume,oops) <- parseProperty e0

    -- Free variables, but do not count =:=, proveBool, oops or arguments
    let free (lhs :== rhs) = filter (`notElem` (vars ++ ty_vars)) (exprFVs lhs ++ exprFVs rhs)
        free (Total e')    = filter (`notElem` (vars ++ ty_vars)) (exprFVs e')

        get_typeable (lhs :== _) = lhs
        get_typeable (Total e')  = e'

    return $ Property
        { propName       = idToStr prop_name
        , propLiteral    = lit
        , propAssume     = assume
        , propVars       = [ (x,varType x) | x <- vars ]
        , propType       = exprType (get_typeable lit)
        , propRepr       = show assume ++ " ==> " ++ show lit
        , propVarRepr    = map showOutputable vars
        , propOrigin     = UserStated
        , propFunDeps    = nub $ concatMap free (lit:assume)
        , propOffsprings = return []
        , propOops       = oops
        }
trProperty _ = Nothing

totalityProperty :: Var -> Totality -> Maybe (Property Void)
totalityProperty v t = case t of
    Partial  -> Nothing
    Variable -> Nothing
    PER.Total _allowed_to_be_partial -> do
        args <- m_args
        return $ Property
            { propName       = "Totality for " ++ showOutputable v
            , propLiteral    = Total (apps (Var v) (map Var args))
            , propAssume     = [ Total (Var arg)
                               | (_x,arg) <- zip ([0..] :: [Int]) args
                         --      , x `notElem` allowed_to_be_partial
                               ]
            , propVars       = [ (x,varType x) | x <- args ]
            , propType       = snd $ splitFunTys $ varType v
            , propRepr       = "Totality for " ++ showOutputable v
            , propVarRepr    = map showOutputable args
            , propOrigin     = Totality t
            , propFunDeps    = [v]
            , propOffsprings = return []
            , propOops       = False
            }
      where
        m_args = case realIdUnfolding v of
            CoreUnfolding {uf_tmpl} -> case collectTyAndValBinders uf_tmpl of
                (_,xs,_) -> Just (zipWith (\u x -> setVarType u (varType x)) varNames xs)
            _ -> Nothing

apps :: CoreExpr -> [CoreExpr] -> CoreExpr
apps = foldl App

