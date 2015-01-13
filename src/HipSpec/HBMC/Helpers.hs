{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, ViewPatterns, PatternGuards, GADTs, RecordWildCards #-}
module HipSpec.HBMC.Helpers where

import qualified Data.Foldable as F

import HipSpec.HBMC.Utils hiding (lift)

import HipSpec.Pretty

import HipSpec.Lang.Rich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.Type

import HipSpec.Id hiding (Derived(Case))

import Data.Generics.Geniplate

import Data.List
import HipSpec.Utils

import Data.Maybe
import Control.Monad.State

{-
   data Ty = Ty :-> Ty | A

Makes new data types:

   data Lbl_Ty = Lbl_Arrow | Lbl_A

   data D_Ty = D_Ty (Data Lbl_Ty (T2 (Thunk D_Ty) (Thunk D_Ty)))

Makes new constructor functions:

   conArrow = \ a b -> this (D_Ty (Con (val Lbl_Arrow) (T2 a b)))
   conA     = D_Ty (Con (val Lbl_A) (T2 (err "conA") (err "conA")))

Makes new instances for getting the values and arguments:

   instance Value D_Ty where
     type Type D_Ty = Ty

     get (D_Ty (Con cn args)) =
       do l <- get cn
          case (l, args) of
            (Lbl_Arrow, T2 (a) (b)) ->
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

{-
   instance Argument Ty where
     argument Lbl_Arrow (Tuple [a,b]) = [a,b]
     argument Lbl_A     (Tuple [_,_]) = []
     argument _         _             = error "Argument T"
     -}

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

    newList :: Int -> H a -> H (DList a)
    newList s e =
        newVal ((++) (Lbl_Nil:[]) (if (==) s 0 then [] else (Lbl_Cons:[]))
        >>= \ cn  ->
        choose  cn $ \ c ->
            case c of
                Lbl_Cons -> do
                    x <- e
                    xs <- newList (pred s)
                    return (conCons x xs)
                Lbl_Nil -> return (conNil)

    (parameterised on creation functions of polymorphic components)

-}

type DataInfo = [(Id,(Id,[Int]))]

allocateDatatype :: Datatype Id -> (DataInfo,[Type Id])
allocateDatatype (Datatype tc _tvs cons _) = (indexes,types)
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

-- Changes type constructors to Thunk (D_ ..)
typeReplace :: Type Id -> Type Id
typeReplace (TyCon tc ts) = thunkTy (TyCon (d tc) (map typeReplace ts))
typeReplace (ArrTy t1 t2) = typeReplace t1 `ArrTy` typeReplace t2
typeReplace (TyVar a)     = TyVar a
typeReplace Integer       = Integer

derive :: [String] -> [Type Id]
derive xs = [ TyCon (raw x) [] | x <- xs ]

mergeDatatype :: Datatype Id -> (DataInfo,([Datatype Id],[Function Id]))
mergeDatatype dc@(Datatype tc tvs cons _) = (indexes,([labels,ndata],constructors))
  where
    (indexes,args) = allocateDatatype dc

    labels = Datatype (label tc) []
        [ Constructor (label c) []
        | Constructor c _args <- cons
        ]
        (derive (map ("Prelude." ++) ["Ord","Eq","Show"]))

    ndata = Datatype (d tc) tvs
        [ Constructor (d tc)
            [ TyCon hdata
                [ TyCon (label tc) []
                , TyCon (hid (TupleTyCon n)) (map (liftTy . typeReplace) args)
                ]
            ]
        ]
        [] -- (derive ["Prelude.Show","Symbolic.Choice","Symbolic.Equal"])

    n = length args

    constructors = concat
        [ [ Function (constructor c) unpty $ makeLambda [ (n,unty) | Just n <- names ] $
              gbl this `App`
              gbl (d tc) `App`
              (gbl con `apply`
                  [ gbl val `App` gbl (label c)
                  , tuple [ maybe (errorf (show c)) lcl a | a <- names ]
                  ])
          , Function (isA c) unpty $ makeLambda [(xs,unty),(h,unty)] $
              (gbl force `App` lcl xs) `rawBind`
              (makeLambda [(i,unty)] $
                unaryCase (lcl i) (d tc) [lbl,args] $
                   (gbl must `App` (lcl lbl =? c)) `App`
                   (lcl h `apply` [ gbl (HBMCId $ Select j n) `App` lcl args | j <- ixs {-??-} ]))
          ]
        | Constructor c _cargs <- cons
        , let Just ixs = fmap snd (lookup c indexes)
        , let xs = refresh c (-1)
        , let h   = raw "h"
        , let i   = raw "i"
        , let lbl = raw "l"
        , let args = raw "args"
        , let names =
                [ if i `elem` ixs
                    then Just (refresh c (fromIntegral i))
                    else Nothing
                | i <- [0..n-1]
                ]
        ]

valueClass x = TyCon (api "Value") [x]
argumentClass x = TyCon (api "Argument") [x]

mkGet :: Datatype Id -> Fresh (Instance Id)
mkGet dc@(Datatype tc tvs _cons _) = do
    fn <- mk_fn
    let tvs' = map TyVar tvs
    -- instance Value a => Value (D_List a) where
    --   type Type (D_List a) = [] (Type a)
    --   get = ...
    return $ Instance
        (map valueClass tvs')
        (valueClass (TyCon (d tc) tvs'))
        [(raw "Type",TyCon (d tc) tvs',TyCon tc (map (\ tv -> TyCon (api "Type") [tv]) tvs'))]
        [fn]
  where
    (indexes,_) = allocateDatatype dc

    n = maximumIndex indexes

    mk_fn = Function (raw "get") unpty <$> do
        s <- tmp
        Lam s unty <$> do
            unD tc (lcl s) $ \ e' -> do
                cn <- newTmp "cn"
                args <- newTmp "args"
                label <- newTmp "lbl"
                lambda_body <- dataCase args label =<< sequence
                    [ do vars <- replicateM n (newTmp "v")
                         let locs = take n (indexed (vars `zip` ixs))
                         get_names <- sequence [ (,) i <$> newTmp "z" | i <- catMaybes locs ]
                         rhs <- foldM
                            (\ inner (i,z) -> (gbl (genericGet) `App` lcl i) `bind` Lam z unty inner)
                            (ret (gbl c `apply` map (lcl . snd) get_names))
                            get_names
                         return (c,locs,rhs)

                    | (c,(_tc,ixs)) <- indexes
                    -- assert tc == _tc
                    , let Just ixs = fmap snd (lookup c indexes)
                    ]
                unaryCase e' con [cn,args] <$>
                    (gbl genericGet `App` lcl cn) `bind` Lam label unty lambda_body

{-
mkArgument :: Datatype Id -> Fresh (Instance Id)
mkArgument dc@(Datatype tc tvs _cons _) = do
    fn <- mk_fn
    -- instance Argument Lbl_List where
    --   argument = ...
    return $ Instance [] (argumentClass (TyCon (label tc) [])) [] [fn]
  where
    (indexes,_) = allocateDatatype dc

    n = maximumIndex indexes

    mk_fn = Function (raw "argument") unpty <$> do

        lbl   <- newTmp "lbl"
        tuple <- newTmp "tuple"
        list  <- newTmp "list"
        args  <- replicateM n (newTmp "arg")

        let brs = [ (pat (label k) [],listLit [ lcl (args !! i) |  i <- ixs ])
                  | (k,(_tc,ixs)) <- indexes
                  ]

        makeLambda ([lbl,tuple] `zip` repeat unty) .
            unaryCase (lcl tuple) tupleStruct [list] <$>
                listCase (lcl list) args (Case (lcl lbl) Nothing brs)
                -}

{-
mkNew :: Datatype Id -> Fresh (Function Id)
mkNew dc@(Datatype tc tvs cons _) = Function (new tc) unpty <$> do

    s <- newTmp "s"
    arg_new <- sequence [ newTmp "mk" | _ <- tvs ]

    let labels = concats
            [ (if any (tc `F.elem`) args then singletonIf (nonZero (lcl s)) else listLit . return)
              (gbl (label c))
            | Constructor c args <- cons
            ]

    cn <- newTmp "cn"

    let (indexes,types) = allocateDatatype dc

    let new_ty t@(_ `ArrTy` _) = error $ "Cannot handle exponential data types" ++ show t
        new_ty Integer         = gbl (api "newNat") `App` gbl_depth
        new_ty (TyVar a) | Just i <- elemIndex a tvs = lcl (arg_new !! i)
        new_ty (TyCon tc' args) = gbl (new tc') `apply` (size:map new_ty args)
          where
            size | tc' == tc = gbl (prelude "pred") `App` lcl s
                 | otherwise = gbl_depth

    let args =
            [ (if tc `F.elem` t
                then \ x -> gbl (api "bara") `apply` [nonZero (lcl s),x]
                else \ x -> gbl (prelude "fmap") `apply` [gbl (api "The"),x])
              (new_ty t)
            | t <- types
            ]

    arg_named <- sequence [ (,) a <$> newTmp "r" | a <- args ]

    let result =
            ret (gbl (d tc) `App`
                     (gbl con `apply` [lcl cn,tuple (map (lcl . snd) arg_named)]))

    make_arguments <- foldM
        (\ e (arg_mk,name) -> arg_mk `bind` Lam name unty e)
        result
        arg_named

    makeLambda ((s:arg_new) `zip` repeat unty) <$> do
        (gbl (api "newVal") `App` labels) `bind` Lam cn unty make_arguments
        --        [lcl cn,Lam c unty (Case (lcl c) Nothing brs)])

-}

-- unD tc e k = case e of { D_tc s -> k s }
unD :: Id -> Expr Id -> (Expr Id -> Fresh (Expr Id)) -> Fresh (Expr Id)
unD tc e k = do
    s <- tmp
    rhs <- k (lcl s)
    return (unaryCase e (d tc) [s] rhs)

-- dataCase arg_tuple lbl_var
--    (K1 (x1,_)  -> C1
--     K2 (y1,y2) -> C2)
-- =>
-- case arg_tuple of
--    T2 a1 a2 -> case lbl_var of
--      Lbl_K1 -> peek a1 >>= \ x1 -> C1
--      Lbl_K2 -> peek a1 >>= \ y1 -> peek a2 >>= \ y2 -> C1
dataCase :: Id -> Id -> [(Id,[Maybe Id],Expr Id)] -> Fresh (Expr Id)
dataCase arg_tuple lbl_var brs@((_,specimen,_):_) = do
    bound <- sequence [ newTmp "arg" | _ <- specimen ]

    brs' <- sequence
        [ do rhs' <- foldM
                (\ acc (b,maybe_real) -> case maybe_real of
                    Just real -> lcl b `bind` Lam real unty acc
                    Nothing   -> return acc
                )
                rhs
                (bound `zip` real_bound)
             return (pat (label k) [],rhs')
        | (k,real_bound,rhs) <- brs
        ]


    return $ unaryCase
        (lcl arg_tuple)
        (hid $ TupleCon (length bound))
        bound
        (Case (lcl lbl_var) Nothing brs')

-- indexed [(x,2)] = Nothing:Nothing:Just x:Nothing:...
indexed :: [(a,Int)] -> [Maybe a]
indexed []         = repeat Nothing
indexed ((x,i):xs) = replace (indexed xs) i (Just x)

maximumIndex :: DataInfo -> Int
maximumIndex = maximum . (0 :) . map succ . concatMap (snd . snd)

projTC :: Id -> DataInfo -> DataInfo
projTC tc indexes = [ i | i@(_,(tc',_)) <- indexes, tc' == tc ]

