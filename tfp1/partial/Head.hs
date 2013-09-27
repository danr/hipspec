{-# LANGUAGE PatternGuards #-}
module Head where

import HipSpec

head_incomplete ::  [t] -> t
head_incomplete (x:_xs) = x

head_error ::  [t] -> t
head_error (x:_xs) = x
head_error [] = error "head!"

head_undefined ::  [t] -> t
head_undefined (x:_xs) = x
head_undefined [] = undefined

head_pg :: [t] -> t
head_pg xs | x:_ <- xs = x

prop_1 = head_incomplete [] =:= ()
prop_2 = head_error []      =:= ()
prop_3 = head_undefined []  =:= ()
prop_4 = head_pg []         =:= ()

prop_1' = head_incomplete [] =:= True
prop_2' = head_error []      =:= True
prop_3' = head_undefined []  =:= True
prop_4' = head_pg []         =:= True

prop_1'' = head_incomplete [] =:= False
prop_2'' = head_error []      =:= False
prop_3'' = head_undefined []  =:= False
prop_4'' = head_pg []         =:= False

prop_a :: Prop a
prop_a = head_incomplete [] =:= head_error []
prop_b :: Prop a
prop_b = head_undefined []  =:= head_pg    []

prop_a_unit :: Prop ()
prop_a_unit = head_incomplete [] =:= head_error []
prop_b_unit :: Prop ()
prop_b_unit = head_undefined []  =:= head_pg    []

prop_a_bool :: Prop Bool
prop_a_bool = head_incomplete [] =:= head_error []
prop_b_bool :: Prop Bool
prop_b_bool = head_undefined []  =:= head_pg    []
