{-# LANGUAGE RecordWildCards #-}
module HipSpec.Trans.Property where

import HipSpec.Trans.SrcRep
import Test.QuickSpec.Equation

import Type
import CoreSyn
import Var
import TysWiredIn
import CoreFVs
import UniqSet

import Halo.Shared

import Data.List (nub)
import Control.Arrow (second)

data Equality = CoreExpr :== CoreExpr

instance Show Equality where
    show (e1 :== e2) = showOutputable e1 ++ " :== " ++ showOutputable e2

data Prop = Prop
    { propEquality :: Equality
    , propAssume   :: [Equality]
    , propVars     :: [(Var,Type)]
    , propName     :: String
    , propRepr     :: String
    , propQSTerms  :: Equation
    , propFunDeps  :: [Var]
    , propOops     :: Bool
    -- ^ It's an error if this property was provable
    }

instance Show Prop where
    show Prop{..} = concat
        ["Prop "
        ,"{ propEquality = ", show propEquality
        ,", propAssume = ", show propAssume
        ,", propVars = ", showOutputable propVars
        ,", propName = ", show propName
        ,", propRepr = ", show propRepr
        ,", propFunDeps = ", showOutputable propFunDeps
        ,", propOops = ", show propOops
        ,"}"
        ]

inconsistentProp :: Prop
inconsistentProp = Prop
    { propEquality = Var trueDataConId :== Var falseDataConId
    , propAssume   = []
    , propVars     = []
    , propName     = "inconsistencyCheck"
    , propRepr     = "inconsistecy check: this should never be provable"
    , propQSTerms  = error "propQSTerms: inconsistentProp"
    , propFunDeps  = []
    , propOops     = True
    }

parseProperty :: CoreExpr -> Maybe (Equality,[Equality],Bool)
parseProperty e = case second trimTyArgs (collectArgs e) of
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

trProperty :: CoreBind -> Maybe Prop
trProperty (NonRec prop_name e) = do
    let (ty_vars,vars,e0) = collectTyAndValBinders e

    (eq,assume,oops) <- parseProperty e0

    -- Free variables, but do not count =:=, proveBool, oops or arguments
    let free (lhs :== rhs) = filter (`notElem` (vars ++ ty_vars)) $ exprFVs lhs ++ exprFVs rhs

    return $ Prop
        { propName     = idToStr prop_name
        , propEquality = eq
        , propAssume   = assume
        , propVars     = [ (x,varType x) | x <- vars ]
        , propRepr     = show assume ++ " ==> " ++ show eq
        , propQSTerms  = error "trProperty : propQSTerms"
        , propFunDeps  = nub $ concatMap free (eq:assume)
        , propOops     = oops
        }
trProperty _ = Nothing
