{-

    All lemmas and generalizations from the article.

-}
module LemmasAndGeneralizations where

import HipSpec.Prelude
import Prelude(Bool(..))
import Definitions

-- Lemmas

prop_L01 :: Nat -> Nat -> Prop Nat
prop_L01 x y = x + S y =:= S (x + y)

prop_L02 :: [a] -> a -> [a] -> Prop Nat
prop_L02 x y z = length (x ++ (y:z)) =:= S (length (x ++ z))

prop_L03 :: [a] -> a -> Prop Nat
prop_L03 x y = length (x ++ [y]) =:= S (length x)

prop_L04 :: Nat -> a -> [a] -> Nat -> Prop [a]
prop_L04 x y z w = drop (S w) (drop x (y:z)) =:= drop w (drop x z)

prop_L05 :: a -> a -> [a] -> Nat -> Nat -> Prop [a]
prop_L05 x y z w v = drop (S v) (drop (S w) (x:y:z)) =:= drop (S v) (drop w (x:z))

prop_L06 :: Nat -> a -> [a] -> Nat -> Nat -> Prop [a]
prop_L06 x y z w v = drop (S v) (drop w (drop x (y:z))) =:= drop v (drop w (drop x z))

prop_L07 :: a -> a -> [a] -> Nat -> Nat -> Nat -> Prop [a]
prop_L07 x y z w v u = drop (S u) (drop v (drop (S w) (x:y:z))) =:= drop (S u) (drop v (drop w (x:z)))

prop_L08 :: [a] -> a -> Prop [a]
prop_L08 x y = rev (x ++ ([y])) =:= y:rev x

prop_L09 :: [a] -> [a] -> a -> Prop [a]
prop_L09 x y z = rev (x ++ (y ++ [z])) =:= z:rev (x ++ y)

prop_L10 :: [a] -> a -> Prop [a]
prop_L10 x y = rev ((x ++ [y]) ++ []) =:= y:rev (x ++ [])

prop_L11 :: [a] -> a -> [a] -> Prop [a]
prop_L11 x y z = (x ++ [y]) ++ z =:= x ++ (y:z)

prop_L12 :: Nat -> [Nat] -> Prop Bool
prop_L12 x y = givenBool (sorted y) (proveBool (sorted (insert x y)))

prop_L13 :: [a] -> [a] -> a -> Prop [a]
prop_L13 x y z = (x ++ y) ++ [z] =:= x ++ (y ++ [z])

prop_L14 :: a -> a -> [a] -> [a] -> Prop Bool
prop_L14 x y z w = even (length (w ++ z)) =:= even (length (w ++ (x:y:z)))

prop_L15 :: a -> a -> [a] -> [a] -> Prop Nat
prop_L15 x y z w = length (w ++ (x:y:z)) =:= S (S (length (w ++ z)))

prop_L16 :: Nat -> Nat -> Prop Bool
prop_L16 x y = even (x + y) =:= even (x + S (S y))

prop_L17 :: Nat -> Nat -> Prop Nat
prop_L17 x y = x + S (S y) =:= S (S (x + y))

prop_L18 :: Nat -> [Nat] -> Prop Nat
prop_L18 x y = length (insert x y) =:= S (length y)

prop_L19 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_L19 x y z = givenBool (x /= y)
               ( givenBool (x `elem` insert y z)
               ( proveBool (x `elem` z)))

prop_L20 :: Nat -> [Nat] -> Prop Nat
prop_L20 x y = count x (insert x y) =:= S (count x y)

prop_L21 :: Nat -> Nat -> [Nat] -> Prop Nat
prop_L21 x y z = givenBool (x /= y) (count x (insert y z) =:= count x z)

prop_L22 :: [a] -> [a] -> [a] -> Prop [a]
prop_L22 x y z = (x ++ y) ++ z =:= x ++ (y ++ z)

prop_L23 :: Nat -> Nat -> Nat -> Prop Nat
prop_L23 x y z = (x * y) * z =:= x * (y * z)

prop_L24 :: Nat -> Nat -> Nat -> Prop Nat
prop_L24 x y z = (x + y) + z =:= x + (y + z)


-- Generalizations

prop_G01 :: [a] -> [a] -> Prop [a]
prop_G01 x y = rev x ++ y =:= qrev x y

{-
prop_G02 :: [a] -> [a] -> Prop [a]
prop_G02 x y = revflat x ++ y =:= qrevflat x y
-}

prop_G03 :: [a] -> [a] -> Prop [a]
prop_G03 x y = rev (qrev x y) =:= rev y ++ x

prop_G04 :: [a] -> [a] -> Prop [a]
prop_G04 x y = rev (qrev x (rev y)) =:= y ++ x

prop_G05 :: [a] -> [a] -> Prop [a]
prop_G05 x y = rev (rev x ++ y) =:= rev y ++ x

prop_G06 :: [a] -> [a] -> Prop [a]
prop_G06 x y = rev (rev x ++ rev y) =:= y ++ x

prop_G07 :: [a] -> [a] -> Prop [a]
prop_G07 x y = qrev (qrev x y) [] =:= rev y ++ x

prop_G08 :: [a] -> [a] -> Prop [a]
prop_G08 x y = qrev (qrev x (rev y)) [] =:= y ++ x

prop_G09 :: [a] -> [a] -> Prop [a]
prop_G09 x y = rotate (length x) (x ++ y) =:= y ++ x

prop_G10 :: Nat -> Nat -> Prop Nat
prop_G10 x y = fac x * y =:= qfac x y

prop_G11 :: Nat -> Nat -> Nat -> Prop Nat
prop_G11 x y z = x * y + z =:= mult x y z

prop_G12 :: Nat -> Nat -> Nat -> Prop Nat
prop_G12 x y z = exp x y * z =:= qexp x y z

lemmas =
    ( prop_L01
    , prop_L02
    , prop_L03
    , prop_L04
    , prop_L05
    , prop_L06
    , prop_L07
    , prop_L08
    , prop_L09
    , prop_L10
    , prop_L11
    , prop_L12
    , prop_L13
    , prop_L14
    , prop_L15
    , prop_L16
    , prop_L17
    , prop_L18
    , prop_L19
    , prop_L20
    , prop_L21
    , prop_L22
    , prop_L23
    , prop_L24
    )

generalizations =
   ( prop_G01
--  , prop_G02
   , prop_G03
   , prop_G04
   , prop_G05
   , prop_G06
   , prop_G07
   , prop_G08
   , prop_G09
   , prop_G10
   , prop_G11
   , prop_G12
   )
