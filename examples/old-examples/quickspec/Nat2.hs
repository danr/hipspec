{-# LANGUAGE DeriveDataTypeable, TypeFamilies, CPP #-}
module Main where

import Data.Typeable

import Hip.HipSpec

import Test.QuickCheck hiding (Prop)
import Test.QuickSpec

import Prelude hiding ((+),(*),even,odd,pred,sum,id)
import qualified Prelude as P

data Nat = Z | S Nat deriving (Show,Eq,Ord,Typeable)


infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
Z   + m = m
-- S n + m = S (n + m)
S n + m = n + S m

(*) :: Nat -> Nat -> Nat
Z   * m = Z
S n * m = m + (n * m)

-- sigma f Z     = Z
-- sigma f (S n) = sigma f n + f (S n)

-- sum xs = sigma id xs
--sum Z     = Z
--sum (S n) = sum n + S n

-- cubes xs = sigma cube xs
--cubes Z     = Z
--cubes (S n) = cubes n + (S n * S n * S n)

-- sq x = x * x

-- id x = x

-- cube x = x * x * x

-- two = S (S Z)

-- one = S Z

prop_comm :: Nat -> Nat -> Prop Nat
prop_comm x y = x + y =:= y + x

main = hipSpec "Nat2.hs" conf 3
  where conf = describe "Nats"
               [ var "x" natType
               , var "y" natType
               , var "z" natType
               , con "Z" Z
               , con "S" S
               , con "+" (+)
               , con "*" (*)
               -- , con "id" (id :: Nat -> Nat)
--                , con "sum" sum
--                , con "cubes" cubes
               -- , con "sigma" sigma
               -- , con "sq" sq
               -- , con "two" two
               -- , con "one" one
               -- , con "cube" cube
               ]
           where natType = (error "Nat type" :: Nat)

-- 4 * sum sq x = sum (sum id) (2 * x)


-- sum x + sum x = x * (S x)


instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (P.pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S x) = variant (-1) . coarbitrary x

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return

  {-

  Failed to prove (x*y)*S y = (x+x)*sum S y.
Failed to prove sq (sum S x) = cube x+sum cube x.
Failed to prove sq x = sum id x+sum S x.
Failed to prove x+sq x = sum S x+sum S x.
Failed to prove (x*y)*S x = (y+y)*sum S x.
Failed to prove (x*y)*S x = sum S x*(y+y).
Failed to prove (x*y)*S y = sum S y*(x+x).
Failed to prove sum (x+) x = sq x+sum id x.
Failed to prove sq x+cube x = (x+x)*sum S x.
Failed to prove sum (x+) y = (x*y)+sum id y.
Failed to prove sum (x+) y = sum id y+(x*y).
Failed to prove sum (y+) x = (x*y)+sum id x.
Failed to prove sum (y+) x = sum id x+(x*y).
Failed to prove sum (x+) x = sum id x+sq x.
Failed to prove sq (sum S x) = sum cube x+cube x.
Failed to prove sq x+cube x = sum S x*(x+x).
Failed to prove sum cube x = sq (sum id x).
Failed to prove sq (sum S x) = sum cube (S x).
Failed to prove sq x = sum S x+sum id x.
Failed to prove sum cube x = sum id x*sum id x.
Failed to prove cube (sum id x) = sum id x*sum cube x.
Failed to prove cube (sum id x) = sum cube x*sum id x.
Proved: x = x+Z,
	Z = x*Z,
	S (x+y) = x+S y,
	sum S x = sum id (S x),
	sum (sum S) x = sum (sum id) (S x),
	x+y = y+x,
	x+(y+z) = y+(x+z),
	x*(y+y) = (x+x)*y,
	(Z*) = sum (Z*),
	x = x*S Z,
	x+(x*y) = x*S y,
	x*y = y*x,
	y*(x+z) = (x*y)+(y*z),
	x*(x*y) = y*sq x,
	y*cube x = sq x*(x*y),
	x*sum S y = sum (x*) (S y),
	sum (x*) y = x*sum id y,
	sum (y*) x = sum id x*y,
	x*(y*z) = y*(x*z)
Unproved: (none)
19/19


17: sum id Z == Z
18: sum id two == one
19: sum id one == Z
20: sum S Z == Z
21: sum S two == S two
22: sum S one == one
23: sum sq Z == Z
24: sum sq two == one
25: sum sq one == Z
26: sum cube Z == Z
27: sum cube two == one
28: sum cube one == Z
29: (x*y)+(x*z) == x*(y+z)
30: cube x*cube y == cube (x*y)
31: sum (x*) (S y) == x*sum S y
32: sum id (S x) == sum S x
33: sum cube (S x) == sq (sum S x)
34: sum (x+) Z == Z
35: sum (x+) two == S (x+x)
36: sum (x+) one == x
37: sum (x*) Z == Z
38: x*sum id y == sum (x*) y
39: sq (sum id x) == sum cube x
40: x+sum id x == sum S x
41: sum (two+) x == x+sum S x
42: sq (S two) == S (cube two)
43: (x*y)+sum id x == sum (y+) x
44: (x+x)*sum S y == (x*y)*S y
45: sum (Z*) (x+y) == Z
46: sum (Z*) (x*y) == Z
47: sq x+sum sq x == sum sq (S x)
48: cube x+sum cube x == sq (sum S x)
49: sum (Z*) (cube x) == Z
50: sum (sum id) (S x) == sum (sum S) x
51: sum S (sq two) == two+cube two
52: sum cube (sq two) == sum S (cube two)
53: sum (sum id) Z == Z
54: sum (sum id) two == Z
55: sum (sum id) one == Z
56: sum (sum S) two == one
57: sum (sum sq) Z == Z
58: sum (sum sq) two == Z
59: sum (sum sq) one == Z
60: sum (sum cube) Z == Z
61: sum (sum cube) two == Z
62: sum (sum cube) one == Z
63: sum id x+sum S x == sq x
64: (x+two)*sum S x == sum (x*) (x+two)
65: sum sq x*sq two == sum (sum id) (x+x)
66: sum (Z*) (sum id x) == Z
67: sum (Z*) (sum S x) == Z
68: sum (Z*) (sum sq x) == Z
69: sum (Z*) (sum cube x) == Z
70: sum (two*) (x+two) == S x*(x+two)
71: sum (two+) (sq two) == sum sq (sq two)
72: sum (sum id) (cube two) == sum (two*) (cube two)
73: sum (sum S) (sq two) == two+cube two
74: sum (sum sq) (S two) == one
75: sum (sum sq) (sq two) == two+sq two
76: sum (sum cube) (S two) == one
77: sum (sum cube) (sq two) == two+cube two

Failed to prove sum (x+) (sq x) = two*sum cube x.
Failed to prove sum (x*) (S x) = (x+two)*sum id x.
Failed to prove sum (sum id) (x+x) = sum sq x*sq two.
Failed to prove S (sum cube two) = sum (sum id) (S two).
Failed to prove sum sq (sq two) = sum (sum S) (sq two).
Failed to prove sum S (sum S two) = sum (sum id) (sq two).
Failed to prove sum S (sum S two) = sum (sum sq) (S two).
Failed to prove sq (sq two) = sum (sum S) (S two).
Failed to prove sum (sum sq) (sq two) = sum (sum S) (sum S two).
Failed to prove cube (x*y) = cube x*cube y.
Failed to prove cube (x*y) = cube y*cube x.
Failed to prove sum cube x = sq (sum id x).
Failed to prove cube (x+x) = cube x*cube two.
Failed to prove sum (x*) (x+two) = (x+two)*sum S x.
Failed to prove sum (x+) (sq x) = sum cube x*two.
Failed to prove cube (x+x) = cube two*cube x.
Failed to prove sum (x+) (sq x) = sum cube x+sum cube x.
Failed to prove sum (x*) (S x) = sum id x*(x+two).
Failed to prove sum cube x = sum id x*sum id x.
Failed to prove cube (sum id x) = sum id x*sum cube x.
Failed to prove sum (x*) (x+two) = sum S x*(x+two).
Failed to prove cube (sum id x) = sum cube x*sum id x.
Failed to prove sum id x+sum cube x = sum (two*) (sum id x).
Failed to prove sum (sum id) (x+x) = sq two*sum sq x.
Failed to prove sq (sum S two) = sum (two+) (sum S two).
Proved: x = x+Z,
	S x = x+one,
	Z = x*Z,
	x = x*one,
	x+two = two+x,
	x+(y+z) = (x+y)+z,
	x+(y+z) = y+(x+z),
	x+(y+z) = z+(x+y),
	x+(x+two) = S x*two,
	x+x = x*two,
	x+(x*y) = x*S y,
	x*y = y*x,
	x*(y+z) = (x*y)+(x*z),
	x*(y*z) = y*(x*z),
	x*(y*z) = z*(x*y),
	(Z*) = sum (Z*),
	sum (y*) x = sum id x*y,
	sum S x = sum id x+x,
	sum (y+) x = (x*y)+sum id x,
	x*(x+two) = sum S x+sum id x,
	x+sq x = sum id x+sum id x
Unproved: (none)
21/21


-}

(=:=) = undefined
type Prop a = a
