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

type Rec a = (a,PolyType a,[Type a])

fixpointInduction :: Params -> ArityMap -> (Id -> Bool) -> Property eq -> [[ProofObligation eq]]
fixpointInduction _p am is_recursive (tvSkolemProp -> (prop@Property{..},sorts,ignore)) =
    [ [ Obligation
        { ob_prop = prop
        , ob_info = ObFixpointInduction
            { fpi_repr =
                let a :=: b = replace_with sel (Gbl . black)
                in  exprRepr (fmap originalId a) ++ " == " ++ exprRepr (fmap originalId b) ++ desc
            }
        , ob_content = calcDepsIgnoring ignore subtheory
            { defines = Conjecture
            , clauses = sorts ++ content
            }
        }
      | (desc,content) <- [("",base sel),(" (step)",step sel)]
      ]
    | sel <- yes_no
    ]
  where
    (recs,replace) = replaceLit is_recursive prop_goal

    yes_no :: [[(Bool,Rec Id)]]
    yes_no = drop 1 $ zipWith zip (replicateM (length recs) [False,True]) (repeat recs)

    replace_with :: [(Bool,Rec Id)] -> (Id -> PolyType Id -> [Type Id] -> Expr Id) -> Literal
    replace_with sel mk_id = replace [ mk_id x t ts | (b,(x,t,ts)) <- sel, b ]

    step sel =
        let cl l mk_id = Clause Nothing [Source] l [] (tr_lits [] (replace_with sel (Gbl . mk_id):prop_assums))
        in  [ cl Axiom white, cl Goal black ]

    tr_lits scope (g:as) =
       forAlls
           [ (P.Id x,trType t) | (x,t) <- prop_vars ]
           ((map (trLiteral am (scope ++ map fst prop_vars)) as)
            ===> trLiteral am (scope ++ map fst prop_vars) g)

    base sel = Clause Nothing [Source] Goal [] $ ny
        [ existss quant (tr_lits quant (replace es:prop_assums))
        | (quant,es) <- cands
        ]
      where
        ny = foldr1 (\/)

        active = [ rec | (b,rec) <- sel, b ]

        cands :: [([(Id,Type Id)],[Expr Id])]
        cands = [ let (iss,es) = unzip c in (concat iss,es) | c <- cands0 ]

        cands0 :: [[([(Id,Type Id)],Expr Id)]]
        cands0 = forM (zip [0..] active) $ \ (i,(x,S.Forall tvs ty,ts)) ->
            let t = S.substManyTys (tvs `zip` ts) ty
                (args,res) = collectArrTy t
            in  [ ([],callConst i args)
                | (i,arg) <- [0..] `zip` args
                , arg == res
                ] ++
                [ ([(v,res)],callConst 0 (res:args) `S.App` Lcl v res)
                | let v = mkLetFrom Eta i x
                ]

callConst :: Int -> [Type a] -> Expr a
callConst i ts = Gbl name ty ts
  where
    name = Const i (length ts)
    ty   = S.Forall tvs (map TyVar tvs `makeArrows` TyVar tvs !! i)
    tvs  = [ mkLetFrom (Derived GenTyVar j) j name | (j,_) <- zip [0..] ts ]

replaceExpr :: Eq a => (a -> Bool) -> Expr a -> ([Rec a],[Expr a] -> Expr a)
replaceExpr ok e0 = case e0 of
    Gbl x t ts | ok x      -> ([(x,t,ts)],\ [u] -> u)
               | otherwise -> ([],\ [] -> e0)
    Lcl{} -> ([],\ [] -> e0)
    Lit{} -> ([],\ [] -> e0)
    S.App e1 e2 -> (r1++r2,\ xs -> x1 (take (length r1) xs) `S.App` x2 (drop (length r1) xs))
      where
        (r1,x1) = replaceExpr ok e1
        (r2,x2) = replaceExpr ok e2


replaceLit :: (Id -> Bool) -> Literal -> ([Rec Id],[Expr Id] -> Literal)
replaceLit ok (e1 :=: e2) = (r1++r2,\ xs -> x1 xs :=: x2 (drop (length r1) xs))
  where
    (r1,x1) = replaceExpr ok e1
    (r2,x2) = replaceExpr ok e2
