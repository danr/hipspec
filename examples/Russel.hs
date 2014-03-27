module Russel where

import HipSpec

russel :: Bool -> Bool
russel x = if russel x then False else True

prop1 x = russel x =:= True
prop2 x = russel x =:= False

prop3 :: Prop Bool
prop3 = True =:= False

