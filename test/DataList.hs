module DataList where

import Prelude(undefined,Bool(..))


iff True  a b = a
iff False a b = b

-- Boolean functions


(&&), (||)       :: Bool -> Bool -> Bool
True  && x       =  x
False && _       =  False
True  || _       =  True
False || x       =  x

not              :: Bool -> Bool
not True         =  False
not False        =  True

otherwise        :: Bool
otherwise        =  True

elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _  _ []         =  False
elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs

filter :: (a -> Bool) -> [a] -> [a]
filter p []                 = []
filter p (x:xs) | p x       = x : filter p xs
                | otherwise = filter p xs

nubBy'                   :: (a -> a -> Bool) -> [a] -> [a]
nubBy' eq []             =  []
nubBy' eq (x:xs)         =  x : nubBy' eq (filter (\ y -> not (eq x y)) xs)

nubBy                   :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq l              = nubBy' l []
  where
    nubBy' [] _         = []
    nubBy' (y:ys) xs
       | elem_by eq y xs = nubBy' ys xs
       | otherwise       = y : nubBy' ys (y:xs)

deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

flip f = \x y -> f y x

foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl f z []     =  z
foldl f z (x:xs) =  foldl f (f z x) xs


unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys        =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

prependToAll            :: a -> [a] -> [a]
prependToAll _   []     = []
prependToAll sep (x:xs) = sep : x : prependToAll sep xs

intersperse             :: a -> [a] -> [a]
intersperse _   []      = []
intersperse sep (x:xs)  = x : prependToAll sep xs

select :: (a -> Bool) -> a -> ([a], [a]) -> ([a], [a])
select p x (ts,fs) | p x       = (x:ts,fs)
                   | otherwise = (ts, x:fs)

foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     =  z
foldr f z (x:xs) =  f x (foldr f z xs)


partition               :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs = foldr (select p) ([],[]) xs

data Ordering = LT | EQ | GT

insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy _   x [] = [x]
insertBy cmp x (y:ys')
 = case cmp x y of
     GT -> y : insertBy cmp x ys'
     _  -> x : y : ys'

foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  =  foldl f x xs
foldl1 _ []      =  undefined




maximumBy               :: (a -> a -> Ordering) -> [a] -> a
maximumBy _ []          =  undefined
maximumBy cmp xs        =  foldl1 maxBy xs
                        where
                           maxBy x y = case cmp x y of
                                       GT -> x
                                       _  -> y


inits                   :: [a] -> [[a]]
inits xs                =  [] : case xs of
                                  []      -> []
                                  x : xs' -> map (\ys -> x : ys) (inits xs')

tails                   :: [a] -> [[a]]
tails xs                =  xs : case xs of
                                  []      -> []
                                  _ : xs' -> tails xs'

subsequences            :: [a] -> [[a]]
subsequences xs         =  [] : nonEmptySubsequences xs

nonEmptySubsequences         :: [a] -> [[a]]
nonEmptySubsequences []      =  []
nonEmptySubsequences (x:xs)  =  [x] : foldr f [] (nonEmptySubsequences xs)
  where f ys r = ys : (x : ys) : r

GT == GT = True
EQ == EQ = True
LT == LT = True
_  == _  = False

x /= y = not (x == y)

f . g = \x -> f (g x)

sortBy cmp = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b (\xs -> a:xs) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge (a:as') (b:bs')
      | a `cmp` b == GT = b:merge (a:as')  bs'
      | otherwise       = a:merge as' (b:bs')
    merge [] bs         = bs
    merge as []         = as


map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs


mergesort :: (a -> a -> Ordering) -> [a] -> [a]
mergesort cmp = mergesort' cmp . map wrap

mergesort' :: (a -> a -> Ordering) -> [[a]] -> [a]
mergesort' _   [] = []
mergesort' _   [xs] = xs
mergesort' cmp xss = mergesort' cmp (merge_pairs cmp xss)

merge_pairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
merge_pairs _   [] = []
merge_pairs _   [xs] = [xs]
merge_pairs cmp (xs:ys:xss) = merge cmp xs ys : merge_pairs cmp xss

merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _   [] ys = ys
merge _   xs [] = xs
merge cmp (x:xs) (y:ys)
 = case x `cmp` y of
        GT -> y : merge cmp (x:xs)   ys
        _  -> x : merge cmp    xs (y:ys)

wrap :: a -> [a]
wrap x = [x]

data Maybe a = Just a | Nothing

unfoldr      :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr f b  =
  case f b of
   Just (a,new_b) -> a : unfoldr f new_b
   Nothing        -> []
