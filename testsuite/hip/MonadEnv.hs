{-# LANGUAGE OverlappingInstances, FlexibleInstances,FlexibleContexts #-}
-- No properties of local yet
module MonadEnv where

import HipPrelude
import Prelude (Int,Eq)

-- Poor man's equality
instance Eq b => Eq (Int -> b)

type Env e a = e -> a

(>>=) :: Env e a -> (a -> Env e b) -> Env e b
f >>= g = \e -> g (f e) e

(>>==) :: Env e a -> (a -> Env e b) -> Env e b
(f >>== g) e = g (f e) e

return :: a -> Env e a
return a e = a

returnl :: a -> Env e a
returnl a = \e -> a


-- Bind with lambda --------------------------------------------------------

prop_return_leftl :: (e -> a) -> Prop (e -> a)
prop_return_leftl f = (f >>= return) =:= f

prop_return_rightl :: (a -> e -> a) -> a -> Prop (e -> a)
prop_return_rightl f a = (return a >>= f) =:= f a

prop_assocl :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> Prop (e -> c)
prop_assocl m f g = ((m >>= f) >>= g) =:= (m >>= (\x -> f x >>= g))

-- Bind without lambda --------------------------------------------------------

prop_return_left :: (e -> a) -> Prop (e -> a)
prop_return_left f = (f >>== return) =:= f

prop_return_right :: (a -> e -> a) -> a -> Prop (e -> a)
prop_return_right f a = (return a >>== f) =:= f a

prop_assoc :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> Prop (e -> c)
prop_assoc m f g = ((m >>== f) >>== g) =:= (m >>== (\x -> f x >>== g))

-- With lambda return ---------------------------------------------------------

prop_returnl_leftl :: (e -> a) -> Prop (e -> a)
prop_returnl_leftl f = (f >>= returnl) =:= f

prop_returnl_rightl :: (a -> e -> a) -> a -> Prop (e -> a)
prop_returnl_rightl f a = (returnl a >>= f) =:= f a

prop_returnl_left :: (e -> a) -> Prop (e -> a)
prop_returnl_left f = (f >>== returnl) =:= f

prop_returnl_right :: (a -> e -> a) -> a -> Prop (e -> a)
prop_returnl_right f a = (returnl a >>== f) =:= f a

-- Let's join and fmap these beasts -------------------------------------------

id x = x

fmapl f m = m >>= (\x -> return (f x))
joinl n = n >>= id
fmap f m = m >>== (\x -> return (f x))
join n = n >>== id

fmaplrl f m = m >>= (\x -> returnl (f x))
joinlrl n = n >>= id
fmaprl f m = m >>== (\x -> returnl (f x))
joinrl n = n >>== id

prop_fmapl_id    :: Prop ((e -> a) -> e -> a)
prop_fmapl_id    = fmapl id =:= id

prop_fmap_id     :: Prop ((e -> a) -> e -> a)
prop_fmap_id     = fmap id =:= id

prop_fmaplrl_idl :: Prop ((e -> a) -> e -> a)
prop_fmaplrl_idl = fmaplrl id =:= id

prop_fmaprl_id   :: Prop ((e -> a) -> e -> a)
prop_fmaprl_id   = fmaprl id =:= id

-- Let's just go with the non-lambda definition
(f . g) x = f (g x)

prop_fmap_comp        :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> c)
prop_fmap_comp f g    = fmap (f . g) =:= fmap f . fmap g

prop_fmaprl_comp      :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> c)
prop_fmaprl_comp f g  = fmaprl (f . g) =:= fmaprl f . fmaprl g

prop_fmapl_comp       :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> c)
prop_fmapl_comp f g   = fmapl (f . g) =:= fmapl f . fmapl g

prop_fmaplrl_comp     :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> c)
prop_fmaplrl_comp f g = fmaplrl (f . g) =:= fmaplrl f . fmaplrl g

main = do
  quickCheck (printTestCase "prop_return_leftl" (prop_return_leftl :: (Int -> Int) -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_return_rightl" (prop_return_rightl :: (Int -> Int -> Int) -> Int -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_assocl" (prop_assocl :: (Int -> Int) -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_return_left" (prop_return_left :: (Int -> Int) -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_return_right" (prop_return_right :: (Int -> Int -> Int) -> Int -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_assoc" (prop_assoc :: (Int -> Int) -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_returnl_leftl" (prop_returnl_leftl :: (Int -> Int) -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_returnl_rightl" (prop_returnl_rightl :: (Int -> Int -> Int) -> Int -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_returnl_left" (prop_returnl_left :: (Int -> Int) -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_returnl_right" (prop_returnl_right :: (Int -> Int -> Int) -> Int -> Prop (Int -> Int)))
  quickCheck (printTestCase "prop_fmapl_id" (prop_fmapl_id :: Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmap_id" (prop_fmap_id :: Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmaplrl_idl" (prop_fmaplrl_idl :: Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmaprl_id" (prop_fmaprl_id :: Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmap_comp" (prop_fmap_comp :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmaprl_comp" (prop_fmaprl_comp :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmapl_comp" (prop_fmapl_comp :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> Int) -> Int -> Int)))
  quickCheck (printTestCase "prop_fmaplrl_comp" (prop_fmaplrl_comp :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> Int) -> Int -> Int)))
