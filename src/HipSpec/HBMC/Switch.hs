{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs #-}
module HipSpec.HBMC.Switch where

import HipSpec.HBMC.Utils hiding (lift)

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import HipSpec.Utils

import Data.Maybe
import Control.Monad.State

{-
   data Ty = Ty :-> Ty | A

Makes new data types:

   data Lbl_Ty = Lbl_Arrow | Lbl_A

   data D_Ty = D_Ty (Data Lbl_Ty (T2 (Lift D_Ty) (Lift D_Ty)))

Makes new constructor functions:

   conArrow = \ a b -> D_Ty (Con (val Lbl_Arrow) (T2 (The a) (The b)))
   conA     = D_Ty (Con (val Lbl_A) (T2 UNR UNR))

Makes new instances for getting the values and arguments:

   instance Value D_Ty where
     type Type D_Ty = Ty

     get (D_Ty (Con cn args)) =
       do l <- get cn
          case (l, args) of
            (Lbl_Arrow, T2 (The a) (The b)) ->
                get a >>= \ x ->
                get b >>= \ y ->
                return (x :-> y)
            (Lbl_A, _) -> return A

     get = \ s -> case s of
        D_Ty d -> case d of
            Con cn args ->
                get cn >>= \ l ->
                case args of
                    T2 u v -> case l of
                        Lbl_Arrow ->
                            peek u >>= \ a ->
                            peek v >>= \ b ->
                            return (a :-> b)
                        Lbl_A -> return A

   instance Argument Ty where
     argument Lbl_Arrow (Tuple [a,b]) = [a,b]
     argument Lbl_A     (Tuple [])    = [] -- ?
     argument _         _             = error "Argument T"

Makes a creation function for values up to a size:

    newDTyp :: Int -> H DTyp
    newDTyp k =
      do cn <- newVal ([Lbl_A] ++ [ Lbl_Arrow | k > 0 ])
         choose cn $ \c ->
           case c of
             TArrow -> do a <- newDTyp (k-1)
                          b <- newDTyp (k-1)
                          return (conArrow a b)
             _ -> return (conA c)

    (could be parameterised on creation functions of polymorphic components)

When we case on something:

     case ty of
        a :-> b -> C1[a,b]
        A       -> C2

    ==>

     case ty of
        D_ty tmp -> switch tmp $ \ lbl args ->
            case args of
                T2 arg1 arg2 -> case lbl of
                    Lbl_Ty ->
                        peek arg1 >>= \ a ->
                        peek arg2 >>= \ b ->
                        C1[a,b]
                    Lbl_A -> C2

When we construct something:

    e1 :-> e2 ==> conArrow e1 e2

Since we have zapped the types at this stage, we check for matches in the
list of constructors.
-}

type DataInfo = [(Id,(Id,[Int]))]

allocateDatatype :: Datatype Id -> (DataInfo,[Type Id])
allocateDatatype (Datatype tc _tvs cons) = (indexes,types)
  where
    types :: [Type Id]
    types = allocate [ args | Constructor _ args <- cons ]

    indexes =
        [ (c,(tc,index args (types `zip` [0..])))
        | Constructor c args <- cons
        ]

    index :: [Type Id] -> [(Type Id,Int)] -> [Int]
    index []     _  = []
    index (a:as) ts = i : index as (l ++ r)
      where
        (l,(_,i):r) = break ((a ==) . fst) ts

mergeDatatype :: Datatype Id -> (DataInfo,([Datatype Id],[Function Id]))
mergeDatatype dc@(Datatype tc tvs cons) = (indexes,([labels,ndata],constructors))
  where
    (indexes,args) = allocateDatatype dc

    labels = Datatype (label tc) tvs
        [ Constructor (label c) []
        | Constructor c _args <- cons
        ]

    ndata = Datatype (d tc) tvs
        [ Constructor (d tc)
            [ TyCon hdata
                [ TyCon (label tc) []
                , TyCon (hid (TupleTyCon n)) (map liftTy args)
                ]
            ]
        ]

    n = length args

    constructors =
        [ Function name unpty $ makeLambda [ (n,unty) | Just n <- names ] $
            gbl (d tc) `App`
            gbl con `apply`
                [ gbl val `App` gbl (label c)
                , gbl (hid (TupleCon n)) `apply`
                    [ maybe (unr unty) (the . lcl) a | a <- names ]
                ]
        | Constructor c _cargs <- cons
        , let name  = constructor c
        , let Just ixs = fmap snd (lookup c indexes)
        , let names =
                [ if i `elem` ixs
                    then Just (refresh name (fromIntegral i))
                    else Nothing
                | i <- [0..n-1]
                ]
        ]

-- unD tc e k = case e of { D_tc s -> k s }
unD :: Id -> Expr Id -> (Expr Id -> Fresh (Expr Id)) -> Fresh (Expr Id)
unD tc e k = do
    s <- tmp
    rhs <- k (lcl s)
    return (Case e Nothing [(pat (d tc) [s],rhs)])

-- dataCase arg_tuple lbl_var
--    (K1 (x1,) -> C1
--     K2 (y1,y2) -> C2)
-- =>
-- case arg_tuple of
--    T2 a1 a2 -> case lbl_var of
--      Lbl_K1 -> peek a1 >>= \ x1 -> C1
--      Lbl_K2 -> peek a1 >>= \ y1 -> peek a2 >>= \ y2 -> C1
dataCase :: Id -> Id -> [(Id,[Maybe Id],Expr Id)] -> Fresh (Expr Id)
dataCase arg_tuple lbl_var brs@((_,specimen,_):_) = do
    bound <- sequence [ tmp | _ <- specimen ]

    brs' <- sequence
        [ do rhs' <- foldM
                (\ acc (b,maybe_real) -> case maybe_real of
                    Just real -> peek (lcl b) `bind` Lam real unty acc
                    Nothing   -> return acc
                )
                rhs
                (bound `zip` real_bound)
             return (pat (label k) [],rhs')
        | (k,real_bound,rhs) <- brs
        ]


    return $ Case (lcl arg_tuple) Nothing
        [ ( pat (hid $ TupleCon (length bound)) bound
          , Case (lcl lbl_var) Nothing brs'
          )
        ]

-- indexed [(x,2)] = Nothing:Nothing:Just x:Nothing:...
indexed :: [(a,Int)] -> [Maybe a]
indexed []         = repeat Nothing
indexed ((x,i):xs) = replace (indexed xs) i (Just x)

maximumIndex :: DataInfo -> [Alt Id] -> Int
maximumIndex indexes brs = maximum . (0 :) . map succ . concat $
    [ ixs
    | (ConPat k _ _ _,_) <- brs
    , let Just (_,ixs) = lookup k indexes
    ]

addSwitches :: TransformBiM Fresh (Expr Id) t => DataInfo -> t -> Fresh t
addSwitches indexes = transformBiM $ \ e0 -> case e0 of

    Gbl c _ _
        | Just (_tc,_ix) <- lookup c indexes
        -> return (gbl (constructor c))

    Case e _mx brs@((ConPat k0 _ _ _,_):_)
        | Just (tc,_) <- lookup k0 indexes -> do

        let n = maximumIndex indexes brs

        let brs' :: [(Id,[Maybe Id],Expr Id)]
            brs' =
                [ (k,take n (indexed (map fst real_args `zip` ixs)),rhs)
                | (ConPat k _ _ real_args,rhs) <- brs
                , let Just (_,ixs) = lookup k indexes
                ]

        lbl_var <- tmp
        arg_tuple <- tmp

        inner <- dataCase arg_tuple lbl_var brs'

        unD tc e $ \ e' -> return $
            gbl switch `apply`
                [ e'
                , makeLambda ([lbl_var,arg_tuple] `zip` repeat unty) inner
                ]

    _ -> return e0

gbl,lcl :: Id -> Expr Id
gbl i = Gbl i unpty []
lcl i = Lcl i unty

pat :: Id -> [Id] -> Pattern Id
pat p as = ConPat p unpty [] (as `zip` repeat unty)

