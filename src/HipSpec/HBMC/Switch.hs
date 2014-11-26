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

     get (DTyp (Con cn args)) =
       do l <- get cn
          case (l, args) of
            (Lbl_Arrow, T2 (The a) (The b)) ->
                get a >>= \ x ->
                get b >>= \ y ->
                return (x :-> y)
            (Lbl_A, _) -> return A

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

addSwitches :: TransformBiM Fresh (Expr Id) t => DataInfo -> t -> Fresh t
addSwitches indexes = transformBiM $ \ e0 -> case e0 of

    Gbl c _ _
        | Just (_tc,_ix) <- lookup c indexes
        -> return (gbl (constructor c))

    Case e _mx brs@((ConPat k0 _ _ _,_):_)
        | Just (tc,_) <- lookup k0 indexes -> do

        let n = maximum . (0 :) . map succ . concat $
                [ ixs
                | (ConPat k _ _ _,_) <- brs
                , let Just (_,ixs) = lookup k indexes
                ]

        args :: [Id] <- replicateM n tmp

        brs' :: [Alt Id] <- sequence
            [ do rhs' <- foldM
                    (\ acc ((real_arg,_arg_ty),arg_ix) ->
                        peek (lcl (args !! arg_ix)) `bind` Lam real_arg unty acc
                    )
                    rhs
                    (real_args `zip` ixs)
                 return (pat (label k) [],rhs')
            | (ConPat k _ _ real_args,rhs) <- brs
            , let Just (_,ixs) = lookup k indexes
            ]

        s :: Id <- tmp
        lbl_var :: Id <- tmp
        arg_tuple :: Id <- tmp

        return $ Case e _mx
            [ ( pat (d tc) [s]
              , gbl switch `apply`
                [ lcl s
                , makeLambda [(lbl_var,unty),(arg_tuple,unty)]
                    (Case (lcl arg_tuple) Nothing
                        [ ( pat (hid $ TupleCon n) args
                          , Case (lcl lbl_var) Nothing brs'
                          )
                        ]
                    )
                ]
              )
            ]

    _ -> return e0

gbl,lcl :: Id -> Expr Id
gbl i = Gbl i unpty []
lcl i = Lcl i unty

pat :: Id -> [Id] -> Pattern Id
pat p as = ConPat p unpty [] (as `zip` repeat unty)

