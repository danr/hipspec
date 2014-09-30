{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.FixpointInduction where

import HipSpec.Translate

import HipSpec.Lang.Simple as S
import HipSpec.Lang.Simple (Type)

import HipSpec.Lang.PolyFOL hiding (Type(..),Term(..))
import qualified HipSpec.Lang.PolyFOL as P
import HipSpec.Lang.ToPolyFOL as P

import Data.Maybe (mapMaybe)

import HipSpec.ThmLib
import HipSpec.Theory
import HipSpec.Params
import HipSpec.Literal
import HipSpec.Property
import HipSpec.Property.Repr

import HipSpec.Pretty

import HipSpec.Id

import qualified HipSpec.Lang.Rich as R

import Data.Generics.Geniplate

import qualified Data.Foldable as F

import Control.Monad

black :: Id -> Id
black f = Derived (f `Fix` B) 0

white :: Id -> Id
white f = Derived (f `Fix` W) 0

isRecursive :: Eq a => Function a -> Bool
isRecursive Function{..} = maybe False (fn_name `F.elem`) fn_body

fixFunction :: Function Id -> [Function Id]
fixFunction fn@Function{..} =
    [ fn
        { fn_name = black fn_name
        , fn_body = (`transformBi` fn_body) $ \ e0 -> case e0 of
            Gbl f t ts | f == fn_name -> Gbl (white fn_name) t ts
            _ -> e0
        }
    , fn
        { fn_name = white fn_name
        , fn_body = Nothing
        }
    ]

fixFunctions :: [Function Id] -> [Function Id]
fixFunctions fs = concat [ fixFunction f | f <- fs, isRecursive f ]

fixpointInduction :: Params -> ArityMap -> (Id -> Bool) -> Property eq -> [ProofObligation eq]
fixpointInduction _p am is_recursive (tvSkolemProp -> (prop@Property{..},sorts,ignore)) =
    [ Obligation
        { ob_prop = prop
        , ob_info = ObFixpointInduction
            { fpi_repr =
                let a :=: b = goal' (Gbl . black)
                in  exprRepr (fmap originalId a) ++ " == " ++ exprRepr (fmap originalId b)
            }
        , ob_content = calcDepsIgnoring ignore subtheory
            { defines = Conjecture
            , clauses = sorts ++ cls goal'
            }
        }
    | goal' <- drop 1 (replaceLit is_recursive prop_goal)
    ]
  where
    cls goal' =
        [ Clause Nothing [Source] Axiom [] (tr_lits (goal' (Gbl . white):prop_assums))
        , Clause Nothing [Source] Goal  [] (tr_lits (goal' (Gbl . black):prop_assums))
        ]
      where
        tr_lits (g:as) =
           forAlls
               [ (P.Id x,trType t) | (x,t) <- prop_vars ]
               ((map (trLiteral am (map fst prop_vars)) as)
                ===> trLiteral am (map fst prop_vars) g)


replaceExpr :: Eq a => (a -> Bool) -> Expr a -> [(a -> PolyType a -> [Type a] -> Expr a) -> Expr a]
replaceExpr ok e0 = case e0 of
    Gbl x t ts  -> [ \ _k -> e0 ] ++ [ \ k -> k x t ts | ok x ]
    Lcl{} -> [ \ _k -> e0 ]
    Lit{} -> [ \ _k -> e0 ]
    S.App e1 e2 ->
        [ \ k -> x1 k `S.App` x2 k
        | x1 <- replaceExpr ok e1
        , x2 <- replaceExpr ok e2
        ]

replaceLit :: (Id -> Bool) -> Literal -> [(Id -> PolyType Id -> [Type Id] -> Expr Id) -> Literal]
replaceLit ok (e1 :=: e2) =
    [ \ k -> x1 k :=: x2 k
    | x1 <- replaceExpr ok e1
    , x2 <- replaceExpr ok e2
    ]

