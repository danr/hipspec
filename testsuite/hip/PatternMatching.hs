module PatternMatching where

import HipPrelude

-- Some different definitions of boolean or
or1 True  b = True
or1 False b = b

or2 True  b = True
or2 a     b = b

or3 False False = False
or3 a     b     = True

{-

prop_or12eq :: Prop (Bool -> Bool -> Bool)
prop_or12eq = or1 =:= or2

prop_or23eq :: Prop (Bool -> Bool -> Bool)
prop_or23eq = or2 =:= or3

prop_or13eq :: Prop (Bool -> Bool -> Bool)
prop_or13eq = or1 =:= or3

-}

data Tree = Leaf | Bin Tree Tree
  deriving (Eq,Show)

instance Arbitrary Tree where
  arbitrary = sized arb
    where arb s = frequency [(1,return Leaf)
                            ,(s,do a <- arb (s `div` 2)
                                   b <- arb (s `div` 2)
                                   return (Bin a b)
                             )]

mirror2fix (Bin a b) = Bin left right
  where
    left = case b of
      Bin l r -> Bin (mirror2fix r) (mirror2fix l)
      Leaf    -> Leaf
    right = case a of
      Bin l r -> Bin (mirror2fix r) (mirror2fix l)
      Leaf    -> Leaf
mirror2fix Leaf = Leaf

mirror2wfix (Bin a b) = Bin left right
  where
    left = case b of
      Bin l r -> Bin (mirror2wfix r) (mirror2wfix l)
      _       -> Leaf
    right = case a of
      Bin l r -> Bin (mirror2wfix r) (mirror2wfix l)
      _       -> Leaf
mirror2wfix _ = Leaf


mirror2 (Bin a b) =
  case a of
    Leaf       -> case b of
                 Bin ba bb -> Bin (Bin (mirror2 bb) (mirror2 ba)) Leaf
                 Leaf       -> Bin Leaf Leaf
    Bin aa ab -> case b of
                 Bin ba bb -> Bin (Bin (mirror2 bb) (mirror2 ba)) (Bin (mirror2 ab) (mirror2 aa))
                 Leaf       -> Bin Leaf (Bin (mirror2 ab) (mirror2 aa))
mirror2 Leaf = Leaf

mirror2w (Bin a b) =
  case a of
    Bin aa ab -> case b of
                 Bin ba bb -> Bin (Bin (mirror2w bb) (mirror2w ba)) (Bin (mirror2w ab) (mirror2w aa))
                 nb        -> Bin nb (Bin (mirror2w ab) (mirror2w aa))
    na      -> case b of
                 Bin ba bb -> Bin (Bin (mirror2w bb) (mirror2w ba)) na
                 nb        -> Bin nb na
mirror2w n = n

mirror (Bin a b) = Bin (mirror b) (mirror a)
mirror Leaf       = Leaf

mirrorw (Bin a b) = Bin (mirrorw b) (mirrorw a)
mirrorw n       = n

{-

prop_tests :: Prop Tree
prop_tests = mirror2 (Bin (Bin undefined undefined) Leaf) =:= Bin Leaf (Bin undefined undefined)

prop_testk :: Prop Tree
prop_testk = mirror2w (Bin (Bin undefined undefined) Leaf) =:= Bin Leaf (Bin undefined undefined)

prop_testp :: Prop Tree
prop_testp = mirror (Bin (Bin undefined undefined) Leaf) =:= Bin Leaf (Bin undefined undefined)

prop_testw :: Prop Tree
prop_testw = mirrorw (Bin (Bin undefined undefined) Leaf) =:= Bin Leaf (Bin undefined undefined)

-}

prop_mirror2fix :: Tree -> Prop Tree
prop_mirror2fix x = mirror2fix (mirror2fix x) =:= x

prop_mirror2wfix :: Tree -> Prop Tree
prop_mirror2wfix x = mirror2wfix (mirror2wfix x) =:= x

{-

prop_mirror2 :: Tree -> Prop Tree
prop_mirror2 x = mirror2 (mirror2 x) =:= x

prop_mirror2w :: Tree -> Prop Tree
prop_mirror2w x = mirror2w (mirror2w x) =:= x

prop_mirror :: Tree -> Prop Tree
prop_mirror x = mirror (mirror x) =:= x

prop_mirrorw :: Tree -> Prop Tree
prop_mirrorw x = mirrorw (mirrorw x) =:= x

prop_eq_w_ :: Prop (Tree -> Tree)
prop_eq_w_ = mirrorw =:= mirror

prop_eq_2_ :: Prop (Tree -> Tree)
prop_eq_2_ = mirror2 =:= mirror

prop_eq_2w_w :: Prop (Tree -> Tree)
prop_eq_2w_w = mirror2w =:= mirrorw

prop_eq_2w_2 :: Prop (Tree -> Tree)
prop_eq_2w_2 = mirror2w =:= mirror2

prop_eq_2wfix_2fix :: Prop (Tree -> Tree)
prop_eq_2wfix_2fix = mirror2wfix =:= mirror2fix

prop_eq_2wfix_ :: Prop (Tree -> Tree)
prop_eq_2wfix_ = mirror2wfix =:= mirror

prop_eq_2fix_w :: Prop (Tree -> Tree)
prop_eq_2fix_w = mirror2wfix =:= mirrorw

prop_eq_2wfix_w :: Prop (Tree -> Tree)
prop_eq_2wfix_w = mirror2wfix =:= mirrorw

prop_eq_2fix_ :: Prop (Tree -> Tree)
prop_eq_2fix_ = mirror2 =:= mirror

-}

main = do
  quickCheck (printTestCase "prop_or12eq"   (prop_or12eq :: Prop (Bool -> Bool -> Bool)))
  quickCheck (printTestCase "prop_or23eq"   (prop_or23eq :: Prop (Bool -> Bool -> Bool)))
  quickCheck (printTestCase "prop_or13eq"   (prop_or13eq :: Prop (Bool -> Bool -> Bool)))
  quickCheck (printTestCase "prop_mirror2"  (prop_mirror2 :: Tree -> Prop Tree))
  quickCheck (printTestCase "prop_mirror2w" (prop_mirror2w :: Tree -> Prop Tree))
  quickCheck (printTestCase "prop_mirror"   (prop_mirror :: Tree -> Prop Tree))
  quickCheck (printTestCase "prop_mirrorw"  (prop_mirrorw :: Tree -> Prop Tree))
  quickCheck (printTestCase "prop_eq_w_"     prop_eq_w_)
  quickCheck (printTestCase "prop_eq_2_"     prop_eq_2_)
  quickCheck (printTestCase "prop_eq_2w_w"   prop_eq_2w_w)
  quickCheck (printTestCase "prop_eq_2w_2"   prop_eq_2w_2)
