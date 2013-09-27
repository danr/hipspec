module Records where

import HipSpec
import Prelude (error,undefined)

data X = X { b :: () } | Y

get_unit :: X -> ()
get_unit = b

upd_unit :: X -> X
upd_unit a = a { b = () }

an_a :: X
an_a = X {}

head :: [a] -> a
head (x:_) = x

prop_get :: Prop ()
prop_get = get_unit Y =:= head []

prop_upd :: Prop X
prop_upd = upd_unit Y =:= error "krash!"

prop_get_an_a :: Prop ()
prop_get_an_a = get_unit an_a =:= ()

prop_an_a :: Prop X
prop_an_a = an_a =:= X undefined
