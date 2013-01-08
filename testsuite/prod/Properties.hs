{-

    All properties, lemmas and generalizations from the article.

    We do not use this file directly, but they are all here for brevity.

-}
module Properties where

import HipSpec.Prelude
import Prelude(Bool(..))
import Definitions

-- Theorems

prop_T1 :: Nat -> Prop Nat
prop_T1 x = double x =:= x + x

prop_T2 :: [a] -> [a] -> Prop Nat
prop_T2 x y = length (x ++ y ) =:= length (y ++ x)

prop_T3 :: [a] -> [a] -> Prop Nat
prop_T3 x y = length (x ++ y ) =:= length (y ) + length x

prop_T4 :: [a] -> Prop Nat
prop_T4 x = length (x ++ x) =:= double (length x)

prop_T5 :: [a] -> Prop Nat
prop_T5 x = length (rev x) =:= length x

prop_T6 :: [a] -> [a] -> Prop Nat
prop_T6 x y = length (rev (x ++ y )) =:= length x + length y

prop_T7 :: [a] -> [a] -> Prop Nat
prop_T7 x y = length (qrev x y) =:= length x + length y

prop_T8 :: Nat -> Nat -> [a] -> Prop [a]
prop_T8 x y z = drop x (drop y z) =:= drop y (drop x z)

prop_T9 :: Nat -> Nat -> [a] -> Nat -> Prop [a]
prop_T9 x y z w = drop w (drop x (drop y z)) =:= drop y (drop x (drop w z))

prop_T10 :: [a] -> Prop [a]
prop_T10 x = rev (rev x) =:= x

prop_T11 :: [a] -> [a] -> Prop [a]
prop_T11 x y = rev (rev x ++ rev y) =:= y ++ x

prop_T12 :: [a] -> [a] -> Prop [a]
prop_T12 x y = qrev x y =:= rev x ++ y

prop_T13 :: Nat -> Prop Nat
prop_T13 x = half (x + x) =:= x

prop_T14 :: [Nat] -> Prop Bool
prop_T14 x = proveBool (sorted (isort x))

prop_T15 :: Nat -> Prop Nat
prop_T15 x = x + S x =:= S (x + x)

prop_T16 :: Nat -> Prop Bool
prop_T16 x = proveBool (even (x + x))

prop_T17 :: [a] -> [a] -> Prop [a]
prop_T17 x y = rev (rev (x ++ y)) =:= rev (rev x) ++ rev (rev y)

prop_T18 :: [a] -> [a] -> Prop [a]
prop_T18 x y = rev (rev x ++ y) =:= rev y ++ x

prop_T19 :: [a] -> [a] -> Prop [a]
prop_T19 x y = rev (rev x) ++ y =:= rev (rev (x ++ y))

prop_T20 :: [a] -> Prop Bool
prop_T20 x = proveBool (even (length (x ++ x)))

prop_T21 :: [a] -> [a] -> Prop [a]
prop_T21 x y = rotate (length x) (x ++ y) =:= y ++ x

prop_T22 :: [a] -> [a] -> Prop Bool
prop_T22 x y = even (length (x ++ y)) =:= even (length (y ++ x))

prop_T23 :: [a] -> [a] -> Prop Nat
prop_T23 x y = half (length (x ++ y)) =:= half (length (y ++ x))

prop_T24 :: Nat -> Nat -> Prop Bool
prop_T24 x y = even (x + y) =:= even (y + x)

prop_T25 :: [a] -> [a] -> Prop Bool
prop_T25 x y = even (length (x ++ y)) =:= even (length y + length x)

prop_T26 :: Nat -> Nat -> Prop Nat
prop_T26 x y = half (x + y) =:= half (y + x)

prop_T27 :: [a] -> Prop [a]
prop_T27 x = rev x =:= qrev x []

{-
prop_T28 :: [a] -> Prop [a]
prop_T28 x = revflat x =:= qrevflat x []
-}

prop_T29 :: [a] -> Prop [a]
prop_T29 x = rev (qrev x []) =:= x

prop_T30 :: [a] -> Prop [a]
prop_T30 x = rev (rev x ++ []) =:= x

prop_T31 :: [a] -> Prop [a]
prop_T31 x = qrev (qrev x []) [] =:= x

prop_T32 :: [a] -> Prop [a]
prop_T32 x = rotate (length x) x =:= x

prop_T33 :: Nat -> Prop Nat
prop_T33 x = fac x =:= qfac x one

prop_T34 :: Nat -> Nat -> Prop Nat
prop_T34 x y = x * y =:= mult x y zero

prop_T35 :: Nat -> Nat -> Prop Nat
prop_T35 x y = exp x y =:= qexp x y one

prop_T36 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T36 x y z = givenBool (x `elem` y) (proveBool (x `elem` (y ++ z)))

prop_T37 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T37 x y z = givenBool (x `elem` z) (proveBool (x `elem` (y ++ z)))

prop_T38 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T38 x y z = givenBool (x `elem` y)
               ( givenBool (x `elem` z)
               ( proveBool (x `elem` (y ++ z))))

prop_T39 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_T39 x y z = givenBool (x `elem` drop y z) (proveBool (x `elem` z))

prop_T40 :: [Nat] -> [Nat] -> Prop [Nat]
prop_T40 x y = givenBool (x `subset` y) ((x `union` y) =:= y)

prop_T41 :: [Nat] -> [Nat] -> Prop [Nat]
prop_T41 x y = givenBool (x `subset` y) ((x `intersect` y) =:= x)

prop_T42 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T42 x y z = givenBool (x `elem` y) (proveBool (x `elem` (y `union` z)))

prop_T43 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T43 x y z = givenBool (x `elem` y) (proveBool (x `elem` (z `union` y)))

prop_T44 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T44 x y z = givenBool (x `elem` y)
               ( givenBool (x `elem` z)
               ( proveBool (x `elem` (y `intersect` z))))

prop_T45 :: Nat -> [Nat] -> Prop Bool
prop_T45 x y = proveBool (x `elem` insert x y)

prop_T46 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_T46 x y z = x =:= y ==> proveBool (x `elem` insert y z)

prop_T47 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_T47 x y z = givenBool (x /= y) ((x `elem` insert y z) =:= x `elem` z)

prop_T48 :: [Nat] -> Prop Nat
prop_T48 x = length (isort x) =:= length x

prop_T49 :: Nat -> [Nat] -> Prop Bool
prop_T49 x y = givenBool (x `elem` isort y) (proveBool (x `elem` y))

prop_T50 :: Nat -> [Nat] -> Prop Nat
prop_T50 x y = count x (isort y) =:= count x y


-- Lemmas

prop_L1 :: Nat -> Nat -> Prop Nat
prop_L1 x y = x + S y =:= S (x + y)

prop_L2 :: [a] -> a -> [a] -> Prop Nat
prop_L2 x y z = length (x ++ (y:z)) =:= S (length (x ++ z))

prop_L3 :: [a] -> a -> Prop Nat
prop_L3 x y = length (x ++ [y]) =:= S (length x)

prop_L4 :: Nat -> a -> [a] -> Nat -> Prop [a]
prop_L4 x y z w = drop (S w) (drop x (y:z)) =:= drop w (drop x z)

prop_L5 :: a -> a -> [a] -> Nat -> Nat -> Prop [a]
prop_L5 x y z w v = drop (S v) (drop (S w) (x:y:z)) =:= drop (S v) (drop w (x:z))

prop_L6 :: Nat -> a -> [a] -> Nat -> Nat -> Prop [a]
prop_L6 x y z w v = drop (S v) (drop w (drop x (y:z))) =:= drop v (drop w (drop x z))

prop_L7 :: a -> a -> [a] -> Nat -> Nat -> Nat -> Prop [a]
prop_L7 x y z w v u = drop (S u) (drop v (drop (S w) (x:y:z))) =:= drop (S u) (drop v (drop w (x:z)))

prop_L8 :: [a] -> a -> Prop [a]
prop_L8 x y = rev (x ++ ([y])) =:= y:rev x

prop_L9 :: [a] -> [a] -> a -> Prop [a]
prop_L9 x y z = rev (x ++ (y ++ [z])) =:= z:rev (x ++ y)

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

prop_G1 :: [a] -> [a] -> Prop [a]
prop_G1 x y = rev x ++ y =:= qrev x y

{-
prop_G2 :: [a] -> [a] -> Prop [a]
prop_G2 x y = revflat x ++ y =:= qrevflat x y
-}

prop_G3 :: [a] -> [a] -> Prop [a]
prop_G3 x y = rev (qrev x y) =:= rev y ++ x

prop_G4 :: [a] -> [a] -> Prop [a]
prop_G4 x y = rev (qrev x (rev y)) =:= y ++ x

prop_G5 :: [a] -> [a] -> Prop [a]
prop_G5 x y = rev (rev x ++ y) =:= rev y ++ x

prop_G6 :: [a] -> [a] -> Prop [a]
prop_G6 x y = rev (rev x ++ rev y) =:= y ++ x

prop_G7 :: [a] -> [a] -> Prop [a]
prop_G7 x y = qrev (qrev x y) [] =:= rev y ++ x

prop_G8 :: [a] -> [a] -> Prop [a]
prop_G8 x y = qrev (qrev x (rev y)) [] =:= y ++ x

prop_G9 :: [a] -> [a] -> Prop [a]
prop_G9 x y = rotate (length x) (x ++ y) =:= y ++ x

prop_G10 :: Nat -> Nat -> Prop Nat
prop_G10 x y = fac x * y =:= qfac x y

prop_G11 :: Nat -> Nat -> Nat -> Prop Nat
prop_G11 x y z = x * y + z =:= mult x y z

prop_G12 :: Nat -> Nat -> Nat -> Prop Nat
prop_G12 x y z = exp x y * z =:= qexp x y z

