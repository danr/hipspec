module Mutual where

import Prelude ()

data Nat = Succ Nat | Zero
data Bool = True | False

not True      = False
not False     = True

{- This is strange... GHC optimizes this to:

      odd_aa1 = \ ds_da9 ->
           case ds_da9 of _ {
             Succ x_a9W ->
               case x_a9W of _ {
                 Succ x_a9V -> odd_aa1 x_a9V;
                 -- ^ odd now does recursion in depth two

                 Zero -> False
               };
             Zero -> True
           };

      even_aa2 = \ ds_dac ->
           case ds_dac of _ {
             Succ x_a9V ->
               case odd_aa1 x_a9V of _ {
                 -- ^ Where does this case come from?

                 True -> False;
                 False -> True
               };
             Zero -> True
           }

  It's like even has been inlined in odd, and then even has been
  redefined in terms of it. Quite fantastic, but it's not really the
  same program :)

-}

even (Succ x) = not (odd x)
even Zero     = True

odd (Succ x)  = not (even x)
odd Zero      = True