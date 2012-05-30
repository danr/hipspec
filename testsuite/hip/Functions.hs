module Functions where

import HipPrelude
import Prelude ()

const x y = x
flip f x y = f y x
id x = x
s f g x = f x (g x)
k = const

prop_skk_id :: Prop (a -> a)
prop_skk_id = s k k =:= id

prop_skf_id :: (a -> b) -> Prop (a -> a)
prop_skf_id f = s k f =:= id

-- Sometimes, Malin and Mikael help me with names of properties

prop_malins_identity :: b -> a -> Prop a
prop_malins_identity x y = const id x y =:= flip const x y

prop_malins_identity' :: Prop (a -> b -> b)
prop_malins_identity' = const id =:= flip const

prop_mikaels_identity :: (a -> b) -> Prop (a -> b)
prop_mikaels_identity f = id f =:= f

prop_dans_identity :: a -> a -> Prop a
prop_dans_identity x y = const x y =:= id x

--prop_dans_nonidentity :: a -> a -> Prop a
--prop_dans_nonidentity x y = const y x =/= id x

--prop_nonidentity :: a -> Prop (a -> a)
--prop_nonidentity x = const x =/= id

uncurry :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

fst (x,y) = x
snd (x,y) = y

uncurry' :: (a -> b -> c) -> (a,b) -> c
uncurry' f t = f (fst t) (snd t)

prop_uncurry_equal :: Prop ((a -> b -> c) -> (a,b) -> c)
prop_uncurry_equal = uncurry =:= uncurry'

prop_uncurry_f_equal :: (a -> b -> c) -> Prop ((a,b) -> c)
prop_uncurry_f_equal f = uncurry f =:= uncurry' f

-- Only true for finite tuples, by induction (!)
-- Do we need approximation lemma for functions for the two above?
prop_uncurry_f_tuple_equal :: (a -> b -> c) -> (a,b) -> Prop c
prop_uncurry_f_tuple_equal f t = uncurry f t =:= uncurry' f t

prop_uncurry_f_unboxedtuple_equal :: (a -> b -> c) -> a -> b -> Prop c
prop_uncurry_f_unboxedtuple_equal f a b = uncurry f (a,b) =:= uncurry' f (a,b)

curry :: ((a,b) -> c) -> a -> b -> c
curry f a b = f (a,b)

(f . g) x = f (g x)

prop_curry_uncurry :: Prop ((a -> b -> c) -> a -> b -> c)
prop_curry_uncurry = id =:= curry . uncurry

prop_uncurry_curry :: Prop (((a,b) -> c) -> (a,b) -> c)
prop_uncurry_curry = id =:= uncurry . curry

f ... g = \x -> f (g x)

prop_comp_equal :: Prop ((b -> c) -> (a -> b) -> a -> c)
prop_comp_equal = (.) =:= (...)

prop_comp_assoc :: (c -> d) -> (b -> c) -> (a -> b) -> Prop (a -> d)
prop_comp_assoc f g h = ((f . g) . h) =:= (f . (g . h))

--prop_comp_assoc' :: (c -> d) -> (b -> c) -> (a -> b) -> a -> Prop d
--prop_comp_assoc' f g h a = ((f . g) . h) a =:= (f . (g . h)) a

prop_comp_assocl :: (c -> d) -> (b -> c) -> (a -> b) -> Prop (a -> d)
prop_comp_assocl f g h = ((f ... g) ... h) =:= (f ... (g ... h))

prop_left_id :: (a -> b) -> Prop (a -> b)
prop_left_id f = f . id =:= f

prop_right_id :: (a -> b) -> Prop (a -> b)
prop_right_id f = id . f =:= f

prop_left_idl :: (a -> b) -> Prop (a -> b)
prop_left_idl f = f ... id =:= f

prop_right_idl :: (a -> b) -> Prop (a -> b)
prop_right_idl f = id ... f =:= f
