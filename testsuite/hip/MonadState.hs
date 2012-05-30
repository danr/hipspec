{-# LANGUAGE OverlappingInstances, FlexibleInstances,FlexibleContexts #-}
-- Does not yet check put/get properties!
module MonadState where

import HipPrelude
import Prelude (Int,Eq)

-- Poor man's equality
instance Eq b => Eq (Int -> b)


type State s a = s -> (a,s)

uncurry f (a,b) = f a b
uncurry' f t = f (fst t) (snd t)

fst (a,b) = a
snd (a,b) = b

bind_strict :: State s a -> (a -> State s b) -> State s b
(m `bind_strict` f) s = uncurry f (m s)

bind_lazy :: State s a -> (a -> State s b) -> State s b
(m `bind_lazy` f) s = uncurry' f (m s)

bind_let :: State s a -> (a -> State s b) -> State s b
(m `bind_let` f) s = let a  = fst (m s)
                         s' = snd (m s)
                     in  f a s'

bind_strict_lambda :: State s a -> (a -> State s b) -> State s b
m `bind_strict_lambda` f = \s -> uncurry f (m s)

bind_lazy_lambda :: State s a -> (a -> State s b) -> State s b
m `bind_lazy_lambda` f = \s -> uncurry' f (m s)

bind_let_lambda :: State s a -> (a -> State s b) -> State s b
m `bind_let_lambda` f = \s -> let a  = fst (m s)
                                  s' = snd (m s)
                              in  f a s'

return :: a -> State s a
return x s = (x,s)


returnl :: a -> State s a
returnl x = \s -> (x,s)

-- Bind without lambda --------------------------------------------------------

prop_return_left_strict :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left_strict f = (f `bind_strict` return) =:= f

prop_return_left_lazy :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left_lazy f = (f `bind_lazy` return) =:= f

prop_return_left_let :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left_let f = (f `bind_let` return) =:= f

prop_return_right_lazy :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right_lazy f a = (return a `bind_lazy` f) =:= f a

prop_return_right_strict :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right_strict f a = (return a `bind_strict` f) =:= f a

prop_return_right_let :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right_let f a = (return a `bind_let` f) =:= f a

prop_assoc_strict :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc_strict m f g = ((m `bind_strict` f) `bind_strict` g) =:= (m `bind_strict` (\x -> f x `bind_strict` g))

prop_assoc_lazy :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc_lazy m f g = ((m `bind_lazy` f) `bind_lazy` g) =:= (m `bind_lazy` (\x -> f x `bind_lazy` g))

prop_assoc_let :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc_let m f g = ((m `bind_let` f) `bind_let` g) =:= (m `bind_let` (\x -> f x `bind_let` g))

-- Lambda definition ----------------------------------------------------------

prop_return_left_strict_lambda :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left_strict_lambda f = (f `bind_strict_lambda` return) =:= f

prop_return_left_lazy_lambda :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left_lazy_lambda f = (f `bind_lazy_lambda` return) =:= f

prop_return_left_let_lambda :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left_let_lambda f = (f `bind_let_lambda` return) =:= f

prop_return_right_strict_lambda :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right_strict_lambda f a = (return a `bind_strict_lambda` f) =:= f a

prop_return_right_lazy_lambda :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right_lazy_lambda f a = (return a `bind_lazy_lambda` f) =:= f a

prop_return_right_let_lambda :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right_let_lambda f a = (return a `bind_let_lambda` f) =:= f a

prop_assoc_strict_lambda :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc_strict_lambda m f g = ((m `bind_strict_lambda` f) `bind_strict_lambda` g) =:= (m `bind_strict_lambda` (\x -> f x `bind_strict_lambda` g))

prop_assoc_lazy_lambda :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc_lazy_lambda m f g = ((m `bind_lazy_lambda` f) `bind_lazy_lambda` g) =:= (m `bind_lazy_lambda` (\x -> f x `bind_lazy_lambda` g))

prop_assoc_let_lambda :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc_let_lambda m f g = ((m `bind_let_lambda` f) `bind_let_lambda` g) =:= (m `bind_let_lambda` (\x -> f x `bind_let_lambda` g))

-- And the same with return as lambda -----------------------------------------



prop_return_lambda_left_strict :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_lambda_left_strict f = (f `bind_strict` returnl) =:= f

prop_return_lambda_left_lazy :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_lambda_left_lazy f = (f `bind_lazy` returnl) =:= f

prop_return_lambda_right_lazy :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_lambda_right_lazy f a = (returnl a `bind_lazy` f) =:= f a

prop_return_lambda_right_strict :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_lambda_right_strict f a = (returnl a `bind_strict` f) =:= f a

prop_return_lambda_left_let :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_lambda_left_let f = (f `bind_let` returnl) =:= f

prop_return_lambda_right_let :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_lambda_right_let f a = (returnl a `bind_let` f) =:= f a

prop_return_lambda_left_strict_lambda :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_lambda_left_strict_lambda f = (f `bind_strict_lambda` returnl) =:= f

prop_return_lambda_left_lazy_lambda :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_lambda_left_lazy_lambda f = (f `bind_lazy_lambda` returnl) =:= f

prop_return_lambda_left_let_lambda :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_lambda_left_let_lambda f = (f `bind_let_lambda` returnl) =:= f

prop_return_lambda_right_strict_lambda :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_lambda_right_strict_lambda f a = (returnl a `bind_strict_lambda` f) =:= f a

prop_return_lambda_right_lazy_lambda :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_lambda_right_lazy_lambda f a = (returnl a `bind_lazy_lambda` f) =:= f a

prop_return_lambda_right_let_lambda :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_lambda_right_let_lambda f a = (returnl a `bind_let_lambda` f) =:= f a

-- Let's also try something with kliesli-composition

(>=>) :: (a -> State s b) -> (b -> State s c) -> a -> State s c
m >=> n = \a s -> uncurry n (m a s)

prop_right_kliesli :: (a -> s -> (a,s)) -> Prop (a -> s -> (a,s))
prop_right_kliesli f = (f >=> return) =:= f

prop_left_kliesli :: (a -> s -> (a,s)) -> Prop (a -> s -> (a,s))
prop_left_kliesli f = (return >=> f) =:= f

prop_assoc_kliesli :: (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> (c -> s -> (d,s)) -> Prop (a -> s -> (d,s))
prop_assoc_kliesli f g h = ((f >=> g) >=> h) =:= (f >=> (g >=> h))

(>==>) :: (a -> State s b) -> (b -> State s c) -> a -> State s c
m >==> n = \a s -> uncurry' n (m a s)

prop_right_kliesli_strict :: (a -> s -> (a,s)) -> Prop (a -> s -> (a,s))
prop_right_kliesli_strict f = (f >==> return) =:= f

prop_left_kliesli_strict :: (a -> s -> (a,s)) -> Prop (a -> s -> (a,s))
prop_left_kliesli_strict f = (return >==> f) =:= f

prop_assoc_kliesli_strict :: (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> (c -> s -> (d,s)) -> Prop (a -> s -> (d,s))
prop_assoc_kliesli_strict f g h = ((f >==> g) >==> h) =:= (f >==> (g >==> h))


-- Let's join and fmap these beasts -------------------------------------------

id x = x

fmap_strict_lambda f m = m `bind_strict_lambda` (\x -> return (f x))
join_strict_lambda n = n `bind_strict_lambda` id
fmap_lazy_lambda f m = m `bind_lazy_lambda` (\x -> return (f x))
join_lazy_lambda n = n `bind_lazy_lambda` id
fmap_let_lambda f m = m `bind_let_lambda` (\x -> return (f x))
join_let_lambda n = n `bind_let_lambda` id
fmap_strict f m = m `bind_strict` (\x -> return (f x))
join_strict n = n `bind_strict` id
fmap_lazy f m = m `bind_lazy` (\x -> return (f x))
join_lazy n = n `bind_lazy` id
fmap_let f m = m `bind_let` (\x -> return (f x))
join_let n = n `bind_let` id

prop_fmap_id_strict :: Prop ((s -> (a,s)) -> (s -> (a,s)))
prop_fmap_id_strict = fmap_strict id =:= id

prop_fmap_id_lazy :: Prop ((s -> (a,s)) -> (s -> (a,s)))
prop_fmap_id_lazy = fmap_lazy id =:= id

prop_fmap_id_let :: Prop ((s -> (a,s)) -> (s -> (a,s)))
prop_fmap_id_let = fmap_let id =:= id

prop_fmap_id_strict_lambda :: Prop ((s -> (a,s)) -> (s -> (a,s)))
prop_fmap_id_strict_lambda = fmap_strict_lambda id =:= id

prop_fmap_id_lazy_lambda :: Prop ((s -> (a,s)) -> (s -> (a,s)))
prop_fmap_id_lazy_lambda = fmap_lazy_lambda id =:= id

prop_fmap_id_let_lambda :: Prop ((s -> (a,s)) -> (s -> (a,s)))
prop_fmap_id_let_lambda = fmap_let_lambda id =:= id


-- Let's just go with the non-lambda definition
(f . g) x = f (g x)

prop_fmap_comp_strict  :: (b -> c) -> (a -> b) -> Prop ((s -> (a,s)) -> s -> (c,s))
prop_fmap_comp_strict f g  = fmap_strict (f . g) =:= fmap_strict f . fmap_strict g

prop_fmap_comp_lazy  :: (b -> c) -> (a -> b) -> Prop ((s -> (a,s)) -> s -> (c,s))
prop_fmap_comp_lazy f g  = fmap_lazy (f . g) =:= fmap_lazy f . fmap_lazy g

prop_fmap_comp_let  :: (b -> c) -> (a -> b) -> Prop ((s -> (a,s)) -> s -> (c,s))
prop_fmap_comp_let f g  = fmap_let (f . g) =:= fmap_let f . fmap_let g

prop_fmap_comp_strict_lambda :: (b -> c) -> (a -> b) -> Prop ((s -> (a,s)) -> s -> (c,s))
prop_fmap_comp_strict_lambda f g = fmap_strict_lambda (f . g) =:= fmap_strict_lambda f . fmap_strict_lambda g

prop_fmap_comp_lazy_lambda :: (b -> c) -> (a -> b) -> Prop ((s -> (a,s)) -> s -> (c,s))
prop_fmap_comp_lazy_lambda f g = fmap_lazy_lambda (f . g) =:= fmap_lazy_lambda f . fmap_lazy_lambda g

prop_fmap_comp_let_lambda :: (b -> c) -> (a -> b) -> Prop ((s -> (a,s)) -> s -> (c,s))
prop_fmap_comp_let_lambda f g = fmap_let_lambda (f . g) =:= fmap_let_lambda f . fmap_let_lambda g



main = do
  quickCheck (printTestCase "prop_return_left_strict" (prop_return_left_strict :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_right_strict" (prop_return_right_strict :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_strict" (prop_assoc_strict :: (Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_left_lazy" (prop_return_left_lazy :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_right_lazy" (prop_return_right_lazy :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_lazy" (prop_assoc_lazy :: (Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_left_let" (prop_return_left_let :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_right_let" (prop_return_right_let :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_let" (prop_assoc_let :: (Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_left_strict_lambda" (prop_return_left_strict_lambda :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_right_strict_lambda" (prop_return_right_strict_lambda :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_strict_lambda" (prop_assoc_strict_lambda :: (Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_left_lazy_lambda" (prop_return_left_lazy_lambda :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_right_lazy_lambda" (prop_return_right_lazy_lambda :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_lazy_lambda" (prop_assoc_lazy_lambda :: (Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_left_let_lambda" (prop_return_left_let_lambda :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_right_let_lambda" (prop_return_right_let_lambda :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_let_lambda" (prop_assoc_let_lambda :: (Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_left_strict" (prop_return_lambda_left_strict :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_right_strict" (prop_return_lambda_right_strict :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_left_lazy" (prop_return_lambda_left_lazy :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_right_lazy" (prop_return_lambda_right_lazy :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_left_let" (prop_return_lambda_left_let :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_right_let" (prop_return_lambda_right_let :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_left_strict_lambda" (prop_return_lambda_left_strict_lambda :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_right_strict_lambda" (prop_return_lambda_right_strict_lambda :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_left_lazy_lambda" (prop_return_lambda_left_lazy_lambda :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_right_lazy_lambda" (prop_return_lambda_right_lazy_lambda :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_left_let_lambda" (prop_return_lambda_left_let_lambda :: (Int -> (Int,Int)) -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_return_lambda_right_let_lambda" (prop_return_lambda_right_let_lambda :: (Int -> Int -> (Int,Int)) -> Int -> Prop (Int -> (Int,Int))))
  quickCheck (printTestCase "prop_right_kliesli" (prop_right_kliesli :: (Int -> Int -> (Int,Int)) -> Prop (Int -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_left_kliesli" (prop_left_kliesli :: (Int -> Int -> (Int,Int)) -> Prop (Int -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_assoc_kliesli" (prop_assoc_kliesli :: (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> (Int -> Int -> (Int,Int)) -> Prop (Int -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_fmap_id_strict_lambda" (prop_fmap_id_strict_lambda :: Prop ((Int -> (Int,Int)) -> (Int -> (Int,Int)))))
  quickCheck (printTestCase "prop_fmap_id_lazy_lambda" (prop_fmap_id_lazy_lambda :: Prop ((Int -> (Int,Int)) -> (Int -> (Int,Int)))))
  quickCheck (printTestCase "prop_fmap_id_let_lambda" (prop_fmap_id_let_lambda :: Prop ((Int -> (Int,Int)) -> (Int -> (Int,Int)))))
  quickCheck (printTestCase "prop_fmap_id_strict" (prop_fmap_id_strict :: Prop ((Int -> (Int,Int)) -> (Int -> (Int,Int)))))
  quickCheck (printTestCase "prop_fmap_id_lazy" (prop_fmap_id_lazy :: Prop ((Int -> (Int,Int)) -> (Int -> (Int,Int)))))
  quickCheck (printTestCase "prop_fmap_id_let" (prop_fmap_id_let :: Prop ((Int -> (Int,Int)) -> (Int -> (Int,Int)))))
  quickCheck (printTestCase "prop_fmap_comp_strict_lambda" (prop_fmap_comp_strict_lambda :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> (Int,Int)) -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_fmap_comp_lazy_lambda" (prop_fmap_comp_lazy_lambda :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> (Int,Int)) -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_fmap_comp_let_lambda" (prop_fmap_comp_let_lambda :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> (Int,Int)) -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_fmap_comp_strict" (prop_fmap_comp_strict :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> (Int,Int)) -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_fmap_comp_lazy" (prop_fmap_comp_lazy :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> (Int,Int)) -> Int -> (Int,Int))))
  quickCheck (printTestCase "prop_fmap_comp_let" (prop_fmap_comp_let :: (Int -> Int) -> (Int -> Int) -> Prop ((Int -> (Int,Int)) -> Int -> (Int,Int))))

{- more properties for later :)

return . f = fmap f . return

join . fmap join = join . join
join . fmap return = join . return = id
join . fmap (fmap f) = fmap f . join
-}

