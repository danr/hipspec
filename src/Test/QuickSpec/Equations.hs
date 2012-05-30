{-# LANGUAGE GADTs,ScopedTypeVariables #-}
module Test.QuickSpec.Equations where

import Control.Arrow
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Array hiding (range)
import Data.List
import Data.Ord
import Data.Typeable
import qualified Data.Map as Map
import Data.Map(Map)
import System.IO
import System.Random
import Text.Printf
import Test.QuickSpec.Term hiding (evaluate)
import Test.QuickSpec.CongruenceClosure
import Debug.Trace
import qualified Test.QuickSpec.TestTree as T

-- HACK GHC bug
ty1 `eqTypeRep` ty2 =
  f1 == f2 && and (zipWith eqTypeRep tys1 tys2)
  where (f1, tys1) = splitTyConApp ty1
        (f2, tys2) = splitTyConApp ty2

-- Term generation.

type Context = [Symbol]
type Universe = TypeRep -> [Term Symbol]

terms :: Context -> Universe -> Universe
terms ctx base ty =
     [ sym elt
     | elt <- ctx
     , symbolType elt `eqTypeRep` ty
     ]
  ++ [ App f x
     | ty' <- argTypes ctx ty
     , x  <- base ty'
     , not (termIsUndefined x)
     , f  <- terms ctx base (mkFunTy ty' ty)
     , not (termIsUndefined f)
     ]

argTypes ctx ty = [ ty1 | (ty1, ty2) <- funTypes (allTypes ctx),
                          ty2 `eqTypeRep` ty ]
termIsUndefined (Const s) = isUndefined s
termIsUndefined _ = False

terms' :: Context -> Universe -> Universe
terms' ctx base ty = nubSort
     (terms ctx base ty ++
       [ App (Const f) x
       | ty' <- argTypes ctx ty
       , f <- ctx
       , symbolType f `eqTypeRep` mkFunTy ty' ty
       , x <- terms ctx base ty' ])

nubSort :: Ord a => [a] -> [a]
nubSort = map head . partitionBy id

undefinedSyms :: Context -> Context
undefinedSyms = typeNub . concatMap (makeUndefined . symbolClass) . typeNub
  where typeNub = nubBy (\s1 s2 -> symbolType s1 `eqTypeRep` symbolType s2)
        makeUndefined (Data x) =
          Symbol { name = "undefined", label = undefined, description = Nothing,
                   isUndefined = True, typ = TConst, range = return (Data (undefined `asTypeOf` x)) }:
          case funTypes [typeOf x] of
            [] -> []
            _ -> makeUndefined (rhs x)

-- Equivalence class refinement.

data Condition = Always | Symbol :/= Symbol deriving (Eq, Ord, Show)
satisfied :: Ord a => (Symbol -> a) -> Condition -> Bool
satisfied value (a :/= b) = value a /= value b
satisfied value Always = True

partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
partitionBy value = map (map fst) . groupBy (\x y -> snd x == snd y) . sortBy (comparing snd) . map (id &&& value)

-- Pruning.

-- A single unary function doesn't increase depth, but two in a row
-- do.
-- varDepths d (App (Const s) t) = varDepths1 d t
varDepths d t = varDepths1 d t

varDepths1 d (App s t) = varDepths1 d s `merge` varDepths (d-1) t
varDepths1 d (Var x)   = [(x,d)]
varDepths1 d _         = []

[]          `merge` yks = yks
xks         `merge` []  = xks
((x,k):xks) `merge` ((y,n):yns)
  | x < y     = (x,k) : (xks `merge` ((y,n):yns))
  | x == y    = (x, k `min` n) : (xks `merge` yns)
  | otherwise = (y,n) : (((x,k):xks) `merge` yns)

consequences :: (Term Symbol -> Bool) -> Context -> Int -> [(Int, Int, TypeRep)] -> Map Int (Term Symbol) -> [Symbol] -> (Term Int, Term Int) -> [(Term Int, Term Int)]
consequences p ctx d univ univMap rigid (t, u) = cons1 t u `mplus` cons1 u t
    where cons1 t u = do
            s <- mapM substs [ (v,d) | (v, d) <- varDepths d t, v `notElem` rigid ]
            s' <- case rigid of
                    [] -> [[]]
                    [i, j] -> [[(i, Const (label j)), (j, Const (label i))], []]
            guard (ok (s ++ s'))
            let t' = subst (s ++ s') t
                u' = subst (s ++ s') u
            guard (p (unflatten t') && p (unflatten u'))
            return (t', u')
          substs (v, d) = [ (v, Const s) | (_, s, ty) <- takeWhile (\(d', _, _) -> d' <= d) univ, ty `eqTypeRep` symbolType v ]
          ok s = all okAtType (partitionBy (show . symbolType . fst) s)
          okAtType s@((v,_):_) =
            case symbolClass v of
              Data x -> validSubstitution x (map (id *** unflatten) s)
          unflatten t = joinConsts (mapConsts (\s -> Map.findWithDefault (error ("not in map: " ++ show s ++ ", " ++ show univMap)) s univMap) t)

unify (x, y) = do
  x' <- flatten x
  y' <- flatten y
  x' =:= y'

flatten (Var s) = return (label s)
flatten (Const s) = return s
flatten (App t u) = do
  t' <- flatten t
  u' <- flatten u
  t' $$ u'

killSymbols = mapConsts label

prune1 :: (Term Symbol -> Bool) -> Context -> Int -> [(Int, Int, TypeRep)] -> Map Int (Term Symbol) -> [Symbol]
       -> [(Term Symbol, Term Symbol)] -> CC [(Term Symbol, Term Symbol)]
prune1 p ctx d univ univMap rigid es = fmap snd (runWriterT (mapM_ (consider univ) es))
    where consider univ (t, u) = do
            b <- lift (canDerive t u)
            when (not b) $ do
              tell [(t, u)]
              lift (mapM_ unify (consequences p ctx d univ univMap' rigid (killSymbols t, killSymbols u)))
          univMap' = foldr (\s -> Map.insert (label s) (sym s)) univMap ctx

prune2 :: (Term Symbol -> Bool) -> Context -> Int -> [(Int, Int, TypeRep)] -> Map Int (Term Symbol)
       -> [(Term Symbol, Term Symbol)]
       -> [(Term Symbol, Term Symbol)]
       -> [(Term Symbol, Term Symbol)]
prune2 p ctx d univ univMap committed [] = reverse committed
prune2 p ctx d univ univMap committed ((t,u):es) | derivable = prune2 p ctx d univ univMap committed es
                                                 | otherwise = prune2 p ctx d univ univMap ((t,u):committed) es
  where univMap' = foldr (\s -> Map.insert (label s) (sym s)) univMap ctx
        derivable =
          runCCctx ctx $ do
            forM_ (committed ++ es) $ \(t, u) -> mapM_ unify (consequences p ctx d univ univMap' [] (killSymbols t, killSymbols u))
            canDerive t u

loadUniv :: [Term Symbol] -> CC ([(Int, Int, TypeRep)], Map Int (Term Symbol))
loadUniv univ = fmap ((sortBy (comparing (\(d,_,_) -> d)) *** Map.fromList) . unzip . map distr) (mapM f univ)
    where f t = do
            t' <- flatten (killSymbols t)
            return (depth t, t', termType t, t)
          distr (t@(d,x,ty,u)) = ((d, x, ty), (x, u))

type PruneState = (([(Int, Int, TypeRep)], Map Int (Term Symbol)), S)

initPrune :: Context -> [Term Symbol] -> PruneState
initPrune ctx univ0 = runCC (initial (length ctx)) (loadUniv univ0)

doPrune :: (Term Symbol -> Bool) -> Context -> Int -> [(Term Symbol, Term Symbol)] -> [(Condition, [(Term Symbol, Term Symbol)])] -> PruneState -> ([(Condition, Term Symbol, Term Symbol)], PruneState)
doPrune p ctx d es ess ((univ, univMap), s) = (r, ((univ, univMap), s'))
  where (r, s') = runCC s $ do
          es' <- prune1 p ctx d univ univMap [] es
          -- let es'' = prune2 p ctx d univ univMap [] es'
          let es'' = es'
          ess' <- mapM (\(cond, es) -> fmap (map (\(t, u) -> (cond, t, u))) (frozen (prune1 p ctx d univ univMap (condVars cond) es))) ess
          return ([ (Always, t, u) | (t, u) <- es'' ] ++ concat ess')

prune :: (Term Symbol -> Bool) -> Context -> Int -> [Term Symbol] -> [(Term Symbol, Term Symbol)] -> [(Condition, [(Term Symbol, Term Symbol)])] -> [(Condition, Term Symbol, Term Symbol)]
prune p ctx d univ0 es ess =
  fst (doPrune p ctx d es ess (initPrune ctx univ0))

condVars (a :/= b) = [a, b]
condVars Always = []

runCCctx :: Context -> CC a -> a
runCCctx ctx x = evalCC (initial (length ctx)) x

canDerive :: Term Symbol -> Term Symbol -> CC Bool
canDerive t u = do
  t' <- flatten (killSymbols t)
  u' <- flatten (killSymbols u)
  t' =?= u'

subst :: [(Symbol, Term a)] -> Term a -> Term a
subst sub (App s t) = App (subst sub s) (subst sub t)
subst sub t@(Var s) = head ([ t | (v,t) <- sub, s == v ] ++ [ t ])
subst sub s         = s

-- Main program.

genSeeds :: IO [(StdGen, Int)]
genSeeds = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..20])))

-- A definition is something of the form
--   f x1..xn = u
-- where all the xi are distinct variables, there is at least one
-- parameter to f, and if there is an application of f inside u,
-- then one of the xi mustn't appear in that application.
isDefinition (u, t) = typ (fun t) == TConst && all isVar (args t) && not (null (args t)) && nub (args t) == args t && acyclic u
  where isVar (Var _) = True
        isVar _ = False
        isCon (Const _) = True
        isCon _ = False
        acyclic u = all acyclic (args u) && acyclicTop u
        acyclicTop u
          | fun t == fun u = nub (map Var (vars u)) `isProperSubsetOf` args t
          | otherwise = True
        xs `isProperSubsetOf` ys = sort xs `isSublistOf` sort ys && sort xs /= sort ys
        [] `isSublistOf` _ = True
        (x:xs) `isSublistOf` [] = False
        (x:xs) `isSublistOf` (y:ys) | x == y = xs `isSublistOf` ys
                                    | otherwise = (x:xs) `isSublistOf` ys

definitions es = nubBy (\(_, t) (_, t') -> fun t == fun t') (filter isDefinition es)

allOfThem = const True
about xs = any (\s -> description s `elem` map Just xs) . symbols

showType :: TypeRep -> String
showType = show . mapTyCon unqualify
  where unqualify = reverse . takeWhile (/= '.') . reverse

mapTyCon :: (String -> String) -> TypeRep -> TypeRep
mapTyCon f t = mkTyConApp (mkTyCon (f (tyConString tc))) (map (mapTyCon f) ts)
  where (tc, ts) = splitTyConApp t



laws :: Int -> [Symbol] -> t -> (Term Symbol -> Bool) -> (Term Symbol -> Bool) -> IO ()
laws depth ctx0 cond p p' = do
  hSetBuffering stdout NoBuffering
  let ctx = zipWith relabel [0..] (ctx0 ++ undefinedSyms ctx0)
  putStrLn "== API =="
  let putSignature ts = mapM_ putTerms (partitionBy (show . termType) ts)
       where putTerms ts@(t:_) =
               putStrLn (intercalate ", " (map show ts) ++ " :: " ++ showType (termType t))
  putStrLn "-- functions"
  putSignature [ Const elt | elt <- ctx, typ elt == TConst && not (isUndefined elt) ]
  putStrLn "-- variables"
  putSignature [ Var elt | elt <- ctx, typ elt == TVar && not (isUndefined elt) ]
  seeds <- genSeeds
  putStrLn "== classes =="
  cs <- tests p (take 1) depth ctx seeds
  -- error "oops"
  let eqs cond = map head
               $ partitionBy equationOrder
               $ [ (y,x) | x:xs <- map sort cs, funTypes [termType x] == [], y <- xs ]
  printf "%d raw equations.\n\n" (length (eqs Always))
  let univ = filter (not . termIsUndefined) (concat cs)
  printf "Universe has %d terms.\n" (length univ)
  putStrLn "== definitions =="
  sequence_
       [ putStrLn (show i ++ ": "++ show x ++ " := " ++ show y)
       | (i, (y,x)) <- zip [1..] (definitions (eqs Always))
       ]
  putStrLn "== equations =="
  let interesting (_, x, y) = p' x || p' y
      conds = []
      -- conds = [ i :/= j | cond, (i:j:_) <- partitionBy (show . symbolType) (filter (\s -> typ s == TVar) ctx) ]
      pruned = filter interesting (prune p ctx depth univ (eqs Always) [ (cond, eqs cond) | cond <- conds ])
  sequence_
       [ putStrLn (show i ++ ": " ++ concat [ show x ++ "/=" ++ show y ++ " => " | x :/= y <- [cond] ] ++ show y ++ " == " ++ show x)
       | (i, (cond, y,x)) <- zip [1..] pruned
       ]
  forM_ pruned $ \(cond, y, x) -> do
    let c = head (filter (\(x':_) -> x == x') (map sort cs))
        commonVars = foldr1 intersect (map vars c)
        subsumes t = sort (vars t) == sort commonVars
    when (cond == Always && not (any subsumes c)) $
         printf "*** missing term: %s = ???\n"
                (show (mapVars (\s -> if s `elem` commonVars then s else s { name = "_" ++ name s }) x))

test :: (Term Symbol -> Bool) -> Int -> Context -> [(StdGen, Int)] -> (TypeRep -> [Term Symbol]) -> IO [[Term Symbol]]
test p depth ctx seeds base = do
  printf "Depth %d: " depth
  let ts = filter (not . null) [ filter p (terms ctx base ty) | ty <- allTypes ctx ]
  printf "%d terms, " (length (concat ts))
  let evals = [ toValue . eval (memoSym ctx ctxFun) | (ctxFun, toValue) <- map useSeed seeds ]
      tree = map (T.test evals) ts
      cs = concatMap (T.classes . T.cutOff 200) tree
  printf "%d classes, %d raw equations.\n"
         (length cs)
         (sum (map (subtract 1 . length) cs))
  return (sort (map sort cs))

memoSym :: Context -> (Symbol -> a) -> (Symbol -> a)
memoSym ctx f = (arr !) . label
  where arr = listArray (0, length ctx - 1) (map f ctx)

-- tests :: Int -> Context -> [(StdGen, Int)] -> Int -> IO (Int, Classes (Term Symbol))
-- tests 0 _ _ _ = return (0, Classes [] [] [])
-- tests (d+1) ctx vals start = do
--   (n0, cs0) <- tests d ctx vals start
--   let reps = map head (snd (refine start 50 (extract cs0)))
--       base ty = [ t | t <- reps, termType t == ty ]
--   (n, cs) <- test (d+1) ctx vals start base
--   (_, cs1) <- tests d ctx vals n
--   return (n, cs)
-- --  if cs0 == cs1 then return (n, cs) else tests (d+1) ctx vals n

tests :: (Term Symbol -> Bool) -> ([Term Symbol] -> [Term Symbol]) -> Int -> Context -> [(StdGen, Int)] -> IO [[Term Symbol]]
tests p f 0 _ _ = return []
tests p f d ctx vals = do
  cs0 <- tests p f (d-1) ctx vals
  let reps = concatMap f cs0
      base ty = [ t | t <- reps, termType t `eqTypeRep` ty ]
  test p d ctx vals base

traceM :: Monad m => String -> m ()
traceM str = trace str (return ())

congruenceCheck :: Int -> Context -> (Term Symbol -> Bool) -> IO ()
congruenceCheck d ctx0 p = do
  let ctx = zipWith relabel [0..] (ctx0 ++ undefinedSyms ctx0)
  seeds <- genSeeds
  terms <- fmap (sort . map sort) (tests p id d (zipWith relabel [0..] ctx) seeds)
  -- Check: for all f and x, rep (f $$ x) == rep(rep f $$ rep x).
  let reps = Map.unions [ Map.fromList (zip ts (repeat t)) | ts@(t:_) <- terms ]
      rep x = Map.findWithDefault undefined x reps
      defined x = Map.member x reps
  forM_ terms $ \fs@(f:_) ->
    forM_ terms $ \xs@(x:_) ->
      when (defined (App f x)) $ do
        forM_ fs $ \f' ->
          forM_ xs $ \x' -> do
            when (defined (App f' x') && rep (App f' x') /= rep (App f x)) $ do
              putStrLn "Not a congruence relation:"
              sequence_ [ printf "  %s == %s\n" (show t) (show u) | (t, u) <- [(f, f'), (x, x')], t /= u ]
              putStrLn "but"
              printf "  %s /= %s\n" (show (App f x)) (show (App f' x'))
              error "not a congruence relation"

-- For Hipspec
packLaws :: Int -> [Symbol] -> t -> (Term Symbol -> Bool) -> (Term Symbol -> Bool)
         -> IO ([[Term Symbol]],[(Term Symbol,Term Symbol)])
packLaws depth ctx0 cond p p' = do

  let ctx = zipWith relabel [0..] (ctx0 ++ undefinedSyms ctx0)

  seeds <- genSeeds

  classes <- tests p (take 1) depth ctx seeds

  let eqs :: Condition -> [(Term Symbol,Term Symbol)]
      eqs cond = map head
               $ partitionBy equationOrder
               $ [ (y,x) | x:xs <- map sort classes, funTypes [termType x] == [], y <- xs ]

  -- printf "%d raw equations.\n\n" (length (eqs Always))

  let univ = filter (not . termIsUndefined) (concat classes)

  printf "Universe has %d terms.\n" (length univ)

  {-
  putStrLn "== definitions =="

  sequence_
       [ putStrLn (show i ++ ": "++ show x ++ " := " ++ show y)
       | (i, (y,x)) <- zip [1..] (definitions (eqs Always))
       ]
  putStrLn "== equations =="
  -}

  let interesting (_, x, y) = p' x || p' y
      conds = []
      -- conds = [ i :/= j | cond, (i:j:_) <- partitionBy (show . symbolType) (filter (\s -> typ s == TVar) ctx) ]
      pruned = filter interesting (prune p ctx depth univ (eqs Always)
                                         [ (cond, eqs cond) | cond <- conds ])

  return (classes,[ (r,l) | (_,l,r) <- pruned ])
