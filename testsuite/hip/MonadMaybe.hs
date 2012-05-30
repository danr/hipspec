-- Make Prop (a -> b) be transformed to a -> Prop b ?
-- Extensional equality only helps for plain proofs/fixpoint, but not to
-- do approximation lemma or induction
module MonadMaybe where

import HipPrelude
import Prelude ()

data Maybe a = Just a | Nothing

(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
Just x  >>= f = f x
Nothing >>= f = Nothing

return :: a -> Maybe a
return a = Just a

-- Bind -----------------------------------------------------------------------

prop_return_left :: Maybe a -> Prop (Maybe a)
prop_return_left m = (m >>= return) =:= m

prop_return_right :: (a -> Maybe b) -> a -> Prop (Maybe b)
prop_return_right f a = (return a >>= f) =:= f a

prop_assoc :: Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Prop (Maybe c)
prop_assoc m f g = ((m >>= f) >>= g) =:= (m >>= (\x -> f x >>= g))

id x = x

fmap f m = m >>= (\x -> return (f x))

(f . g) x = f (g x)

-- Functor laws ---------------------------------------------------------------

prop_fmap_id :: Prop (Maybe a -> Maybe a)
prop_fmap_id = fmap id =:= id

prop_fmap_comp :: (b -> c) -> (a -> b) -> Prop (Maybe a -> Maybe c)
prop_fmap_comp f g = fmap (f . g) =:= fmap f . fmap g

-- Fmap / return law ----------------------------------------------------------
-- (return is a natural transformation)

prop_fmap_return :: (a -> b) -> Prop (a -> Maybe b)
prop_fmap_return f = return . f =:= fmap f . return

-- Monad laws in terms of join / fmap -----------------------------------------

join m = m >>= id

prop_join_fmap_join :: Prop (Maybe (Maybe (Maybe a)) -> Maybe a)
prop_join_fmap_join = join . fmap join =:= join . join

prop_join_return :: Prop (Maybe a -> Maybe a)
prop_join_return = join . fmap return =:= join . return

prop_join_return_id :: Prop (Maybe a -> Maybe a)
prop_join_return_id = join . return =:= id

prop_fmap_join :: (a -> b) -> Prop (Maybe (Maybe a) -> Maybe b)
prop_fmap_join f = join . fmap (fmap f) =:= fmap f . join

