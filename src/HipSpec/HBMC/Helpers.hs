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
   data Expr = Var Nat | App Expr Expr | Lam Expr

Makes new data types:

   data Lbl_Expr = Lbl_Var | Lbl_App | Lbl_Lam

   newtype D_Expr = D_Expr (Thunk (Data (Lbl_Expr (D_Nat,(D_Expr,D_Expr)))))

Makes new constructor functions:

   conVar = \ a   -> D_Expr (con Lbl_Var (x,(unr,unr)))
   conApp = \ a b -> D_Expr (con Lbl_Var (unr,(a,b)))
   ...

   predApp = \ a b -> equalHere (conApp a b)
   ...

   isApp (D_Expr t) h = isCon Lbl_App t (\ (_,(p,q)) -> h p q)
   ...

   -- -- replaced with Enum+Bounded:
   -- instance ConstructiveData D_Expr where
   --  constrs = [Lbl_Var,Lbl_App,Lbl_Lam]

   instance EqualData D_Expr (D_Nat,(D_Expr,D_Expr)) where
     equalData h =
       [ ([Lbl_Var],        \ (x1,(_,_)) (x2,(_,_)) -> h x1 x2)
       , ([Lbl_Lam,Lbl_App], \(_,(p1,_)) (_,(p2,_)) -> h p1 p2)
       ...
       ]

    instance Value D_Expr where
      type Type D_Expr = Expr

      dflt _ = Var (dflt undefined)

      get (D_Expr t) =
         getData
           (\ lbl args -> case args of
              (x,(p,q)) -> case lbl of
                Lbl_Var -> do n <- get x; return (Var x)
                ...
                Lbl_App -> do a <- get p; b <- get q; return (App a b))
           (Var (dflt undefined))
           t

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

-- Changes type constructors to (D_ ..)
typeReplace :: Type Id -> Type Id
typeReplace (TyCon tc ts) = TyCon (d tc) (map typeReplace ts)
typeReplace (ArrTy t1 t2) = typeReplace t1 `ArrTy` typeReplace t2
typeReplace (TyVar a)     = TyVar a
typeReplace Integer       = Integer

derive :: [Id] -> [Type Id]
derive xs = [ TyCon x [] | x <- xs ]

mergeDatatype :: Datatype Id -> Fresh (DataInfo,([Datatype Id],[Function Id]))
mergeDatatype dc@(Datatype tc tvs cons _) =
    do ctors <- constructors
       return $ (indexes,([labels,ndata],concat ctors))
  where
    (indexes,args) = allocateDatatype dc

    -- data Lbl_Expr = Lbl_Var | Lbl_App | Lbl_Lam
    labels = Datatype (label tc) []
        [ Constructor (label c) []
        | Constructor c _args <- cons
        ]
        (derive (map prelude ["Ord","Eq","Show","Enum","Bounded"]))

    -- newtype D_Expr = D_Expr (Thunk (Data Lbl_Expr (D_Nat,(D_Expr,D_Expr)))))
    ndata = Datatype (d tc) tvs
        [ Constructor (d tc)
            [ thunkTy
                (TyCon hdata
                    [ TyCon (label tc) []
                    , binTupleType (map typeReplace args)
                    ])
            ]
        ]
        (derive (map api ["Constructive","Equal"]))

    n = length args

    constructors = sequence
        [ do names <- sequence
                [ if i `elem` ixs
                    then Just <$> newTmp "x"
                    else return Nothing
                | i <- [0..n-1]
                ]
             sequence
               -- conApp = \ a b -> D_Expr (con Lbl_Var (unr,(a,b)))
               [ return $ Function (mkCon c) unpty $ makeLambda [ (n,unty) | Just n <- names ] $
                   gbl (d tc) `App`
                   (gbl con `apply`
                       [ gbl (label c)
                       , binTupleLit [ maybe (errorf (ppId c)) lcl a | a <- names ]
                       ])

               -- predApp = \ a b -> equalHere (conApp a b)
               , return $ Function (predCon c) unpty $ makeLambda [ (n,unty) | Just n <- names ] $
                  gbl equalHere `App` (gbl (mkCon c) `apply` [ lcl n | Just n <- names ])

               -- isApp (D_Expr t) h = isCon Lbl_App t (\ (_,(p,q)) -> h p q)
               --
               -- isApp =
               --    \ et h ->
               --      case et of
               --        D_Expr t ->
               --          isCon Lbl_App t
               --            (\ arg ->
               --               case arg of
               --                 (unused,rest) ->
               --                   case rest of
               --                     (p,q) -> h p q)
               --
               , do h <- newTmp "h"
                    t <- newTmp "t"
                    et <- newTmp "et"
                    arg <- newTmp "arg"
                    names' <- sequence
                      [ case mn of
                         Just mn -> return mn
                         Nothing -> newTmp "unused"
                      | mn <- names
                      ]
                    lambda <- binTupleCase (lcl arg) names' (lcl h `apply` [ lcl n | Just n <- names ])
                    return $ Function (isCon c) unpty $ makeLambda [(et,unty),(h,unty)] $
                      unaryCase (lcl et) (d tc) [t] $
                        gbl (api "isCon") `apply` [ gbl (label c) , lcl t , Lam arg unty lambda ]
               ]
        | Constructor c _cargs <- cons
        , let Just ixs = fmap snd (lookup c indexes)
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
                            (\ inner (i,z) -> bind z (gbl (genericGet) `App` lcl i) inner)
                            (ret (gbl c `apply` map (lcl . snd) get_names))
                            get_names
                         return (c,locs,rhs)

                    | (c,(_tc,ixs)) <- indexes
                    -- assert tc == _tc
                    , let Just ixs = fmap snd (lookup c indexes)
                    ]
                unaryCase e' con [cn,args] <$>
                    bind label (gbl genericGet `App` lcl cn) lambda_body

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
                    Just real -> bind real (lcl b) acc
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

