{-# LANGUAGE RecordWildCards,NamedFieldPuns,PatternGuards #-}
module HipSpec.Trans.Property
    ( Literal(..)
    , Property(..)
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
import Var
import Id
import TysWiredIn

import Halo.Shared
import Halo.Names (varNames)

import Data.List (nub)
import Data.Function (on)
import Control.Arrow (second)

data Literal
    = CoreExpr :== CoreExpr
    | Total CoreExpr

instance Show Literal where
    show (e1 :== e2) = showOutputable e1 ++ " :== " ++ showOutputable e2
    show (Total e)   = "Total(" ++ showOutputable e ++ ")"

data Property = Property
    { propLiteral    :: Literal
    , propAssume     :: [Literal]
    , propVars       :: [(Var,Type)]
    , propName       :: String
    , propRepr       :: String
    , propVarRepr    :: [String]
    , propQSTerms    :: PEquation
    , propOffsprings :: IO [Property]
    , propFunDeps    :: [Var]
    , propOops       :: Bool
    -- ^ It's an error if this property was provable
    }

instance Eq Property where
    (==) = equal propName .&&. equal (map fst . propVars)

(.&&.) :: (a -> b -> Bool) -> (a -> b -> Bool) -> a -> b -> Bool
(f .&&. g) x y = f x y && g x y

equal :: Eq b => (a -> b) -> a -> a -> Bool
equal = ((==) `on`)

varsFromCoords :: Property -> [Int] -> [String]
varsFromCoords p cs = [ propVarRepr p !! c | c <- cs ]

instance Show Property where
    show Property{..} = concat
        ["Property "
        ,"{ propLiteral = ", show propLiteral
        ,", propAssume = ", show propAssume
        ,", propVars = ", showOutputable propVars
        ,", propName = ", show propName
        ,", propRepr = ", show propRepr
        ,", propFunDeps = ", showOutputable propFunDeps
        ,", propOops = ", show propOops
        ,"}"
        ]

inconsistentProperty :: Property
inconsistentProperty = Property
    { propLiteral    = Var trueDataConId :== Var falseDataConId
    , propAssume     = []
    , propVars       = []
    , propName       = "inconsistencyCheck"
    , propRepr       = "inconsistecy check: this should never be provable"
    , propVarRepr    = []
    , propQSTerms    = error "propQSTerms: inconsistentProp"
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

trProperty :: CoreBind -> Maybe Property
trProperty (NonRec prop_name e) = do
    let (ty_vars,vars,e0) = collectTyAndValBinders e

    (lit,assume,oops) <- parseProperty e0

    -- Free variables, but do not count =:=, proveBool, oops or arguments
    let free (lhs :== rhs) = filter (`notElem` (vars ++ ty_vars)) (exprFVs lhs ++ exprFVs rhs)
        free (Total e')    = filter (`notElem` (vars ++ ty_vars)) (exprFVs e')

    return $ Property
        { propName       = idToStr prop_name
        , propLiteral    = lit
        , propAssume     = assume
        , propVars       = [ (x,varType x) | x <- vars ]
        , propRepr       = show assume ++ " ==> " ++ show lit
        , propVarRepr    = map showOutputable vars
        , propQSTerms    = error "trProperty : propQSTerms"
        , propFunDeps    = nub $ concatMap free (lit:assume)
        , propOffsprings = return []
        , propOops       = oops
        }
trProperty _ = Nothing

totalityProperty :: Var -> Totality -> Maybe Property
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
            , propRepr       = "Totality for " ++ showOutputable v
            , propVarRepr    = map showOutputable args
            , propQSTerms    = error "totalityProperty"
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

