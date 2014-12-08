{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.FixpointInduction where

-- import HipSpec.Translate

import HipSpec.Lang.Simple as S
-- import HipSpec.Lang.Simple (Type)

import HipSpec.Lang.PolyFOL hiding (Type(..),Term(..))
import qualified HipSpec.Lang.PolyFOL as P
import HipSpec.Lang.ToPolyFOL as P

-- import Data.Maybe (mapMaybe)
import Data.List (foldl')

import HipSpec.ThmLib
import HipSpec.Theory
import HipSpec.Params
import HipSpec.Literal
import HipSpec.Property
import HipSpec.Property.Repr

import Data.List.Split (splitOn)

-- import HipSpec.Pretty

import HipSpec.Id

-- import qualified HipSpec.Lang.Rich as R

import Data.Generics.Geniplate

import qualified Data.Foldable as F

import Control.Monad

singleton :: a -> [a]
singleton = return

black :: Id -> Id
black f = Derived (f `Fix` B) 0

white :: Id -> Id
white f = Derived (f `Fix` W) 0

isRecursive :: Eq a => Function a -> Bool
isRecursive Function{..} = True -- maybe False (fn_name `F.elem`) fn_body

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
               ++ [ constFunction i j | j <- [1..maxi arities+1], i <- [0..j-1] ]
  where
    maxi    = foldl' max 0
    arities = map (length . fst . collectArrTy . polytype_inner . fn_type) fs

constFunction :: Int -> Int -> Function Id
constFunction i j = Function {..}
  where
    fn_name = Const i j
    tvs     = [ mkLetFrom (Derived GenTyVar x) x fn_name | x <- [0..toInteger j-1] ]
    fn_args = [ mkLetFrom (Derived Eta x)      x fn_name | x <- [0..toInteger j-1] ]
    fn_type = S.Forall tvs (map TyVar tvs `makeArrows` TyVar (tvs !! i))
    fn_body = Just (Body (Lcl (fn_args !! i) (TyVar (tvs !! i))))

callConst :: Int -> [Type Id] -> Expr Id
callConst i ts = Gbl name ty ts
  where
    Function name ty _ _ = constFunction i (length ts)

type Rec a = (a,PolyType a,[Type a])

fixpointInduction :: Params -> ArityMap -> (Id -> Bool) -> Property -> [[ProofObligation]]
fixpointInduction p am is_recursive0 (tvSkolemProp -> (prop@Property{..},sorts,ignore)) =
    [ [ Obligation
        { ob_prop = prop
        , ob_info = ObFixpointInduction
            { fpi_repr =
                let a :=: b = replace_with sel (Gbl . black)
                in  exprRepr (fmap originalId a) ++ " == " ++ exprRepr (fmap originalId b)
            , fpi_step = is_step
            }
        , ob_content = calcDepsIgnoring ignore subtheory
            { defines = Conjecture
            , clauses = sorts ++ content
            }
        }
      | (is_step,content) <- [(False,base sel),(True,step sel)]
      ]
    | sel <- yes_no
    ]
  where
    is_recursive i = originalId i `elem` concatMap (splitOn ",") (fpi_functions p)

    (recs,replace) = replaceLit is_recursive prop_goal

    yes_no :: [[(Bool,Rec Id)]]
    yes_no = take 24 $ drop 1 $ zipWith zip (replicateM (length recs) [False,True]) (repeat recs)

    replace_with :: [(Bool,Rec Id)] -> (Id -> PolyType Id -> [Type Id] -> Expr Id) -> Literal
    replace_with sel mk_id = replace [ if b then mk_id x t ts else Gbl x t ts | (b,(x,t,ts)) <- sel ]

    tr_vars :: [(Id,Type Id)] -> [(P.Poly Id,P.Type (P.Poly Id) (P.Poly Id))]
    tr_vars qs = [ (P.Id x,trType t) | (x,t) <- qs ]

    tr_lits :: [Id] -> [Literal] -> P.Formula (P.Poly Id) (P.Poly Id)
    tr_lits scope (g:as) =
       forAlls
           (tr_vars prop_vars)
           ((map (trLiteral am (scope ++ map fst prop_vars)) as)
            ===> trLiteral am (scope ++ map fst prop_vars) g)

    step sel =
        let cl l mk_id = Clause Nothing [Source] l [] (tr_lits [] (replace_with sel (Gbl . mk_id):prop_assums))
        in  [ cl Axiom white, cl Goal black ]

    base sel = singleton $ Clause Nothing [Source] Goal [] $ ny
        [ existss (tr_vars quant) (tr_lits (map fst quant) (replace es:prop_assums))
        | (quant,es) <- cands
        ]
      where
        ny = foldr1 (\/)

        cands :: [([(Id,Type Id)],[Expr Id])]
        cands = [ let (iss,es) = unzip c in (concat iss,es) | c <- cands0 ]

        cands0 :: [[([(Id,Type Id)],Expr Id)]]
        cands0 = forM ([0..] `zip` sel) $ \ (i,(active,(x,ty0@(S.Forall tvs ty),ts))) ->
            if active then
                let t = S.substManyTys (tvs `zip` ts) ty
                    (args,res) = collectArrTy t
                in  [ ([],callConst j args)
                    | (j,arg) <- [0..] `zip` args
                    , arg == res
                    ] ++
                    [ ([(v,t)],Lcl v t)
                    | let v = mkLetFrom (Eta `Derived` 1) i x
                    ] ++
                    [ ([(v,res)],callConst 0 (res:args) `S.App` Lcl v res)
                    | let v = mkLetFrom (Eta `Derived` 0) i x
                    ]

                else
                    [ ([],Gbl x ty0 ts) ]

replaceTwo :: (b -> ([r],[e] -> c)) -> (c -> c -> d) -> b -> b -> ([r],[e] -> d)
replaceTwo f mk l r = (r1 ++ r2, \ xs -> x1 (take (length r1) xs) `mk` x2 (drop (length r1) xs))
  where
    (r1,x1) = f l
    (r2,x2) = f r

replaceExpr :: Eq a => (a -> Bool) -> Expr a -> ([Rec a],[Expr a] -> Expr a)
replaceExpr ok e0 = case e0 of
    Gbl x t ts | ok x      -> ([(x,t,ts)],\ [u] -> u)
               | otherwise -> ([],\ [] -> e0)
    Lcl{} -> ([],\ [] -> e0)
    Lit{} -> ([],\ [] -> e0)
    S.App e1 e2 -> replaceTwo (replaceExpr ok) S.App e1 e2

replaceLit :: (Id -> Bool) -> Literal -> ([Rec Id],[Expr Id] -> Literal)
replaceLit ok (e1 :=: e2) = replaceTwo (replaceExpr ok) (:=:) e1 e2

