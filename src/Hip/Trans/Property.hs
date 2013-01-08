{-# LANGUAGE RecordWildCards #-}
module Hip.Trans.Property where

import Hip.Trans.SrcRep
import Test.QuickSpec.Equation

import Type
import CoreSyn
import Var
import TysWiredIn
import CoreFVs
import UniqSet

import Halo.Shared

import Control.Arrow (second)

data Prop = Prop
    { proplhs     :: CoreExpr
    , proprhs     :: CoreExpr
    , propVars    :: [(Var,Type)]
    , propName    :: String
    , propRepr    :: String
    , propQSTerms :: Equation
    , propFunDeps :: [Var]
    , propOops    :: Bool
    -- ^ It's an error if this property was provable
    }

instance Show Prop where
    show Prop{..} = concat
        ["Prop "
        ,"{ proplhs = ", showOutputable proplhs
        ,", proprhs = ", showOutputable proprhs
        ,", propVars = ", showOutputable propVars
        ,", propName = ", show propName
        ,", propRepr = ", show propRepr
        ,", propFunDeps = ", showOutputable propFunDeps
        ,", propOops = ", show propOops
        ,"}"
        ]

inconsistentProp :: Prop
inconsistentProp = Prop
    { proplhs     = Var trueDataConId
    , proprhs     = Var falseDataConId
    , propVars    = []
    , propName    = "inconsistencyCheck"
    , propRepr    = "inconsistecy check: this should never be provable"
    , propQSTerms = error "propQSTerms: inconsistentProp"
    , propFunDeps = []
    , propOops    = True
    }

trProperty :: CoreBind -> Maybe Prop
trProperty (NonRec prop_name e) = do
    let (ty_vars,vars,e0) = collectTyAndValBinders e

        (oops,e_prop) = case second trimTyArgs (collectArgs e0) of
                            (Var x,[prop]) | isOops x -> (True,prop)
                            _                         -> (False,e0)

    (lhs,rhs) <- case second trimTyArgs (collectArgs e_prop) of
                       (Var x,[l,r]) | isEquals x    -> Just (l,r)
                       (Var x,[l])   | isProveBool x -> Just (l,Var trueDataConId)
                       _  -> Nothing

    -- Free variables, but do not count =:=, proveBool, oops or arguments
    let free = filter (`notElem` (vars ++ ty_vars)) $ exprFVs lhs ++ exprFVs rhs

    return $ Prop
        { propName    = idToStr prop_name
        , proplhs     = lhs
        , proprhs     = rhs
        , propVars    = [ (x,varType x) | x <- vars ]
        , propRepr    = showExpr lhs ++ " = " ++ showExpr rhs
        , propQSTerms = error "trProperty : propQSTerms"
        , propFunDeps = free
        , propOops    = oops
        }
trProperty _ = Nothing
