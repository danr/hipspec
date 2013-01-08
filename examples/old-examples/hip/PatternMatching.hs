module PatternMatching where

import Hip.Prelude

-- Some different definitions of boolean or
or1 True  b = True
or1 False b = b

or2 True  b = True
or2 a     b = b

or3 False False = False
or3 a     b     = True

prop_or12eq x y = or1 x y =:= or2 x y

prop_or23eq x y = or2 x y =:= or3 x y

prop_or13eq x y = or1 x y =:= or3 x y

data Tree = Leaf | Bin Tree Tree

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


prop_tests :: Prop Tree
prop_tests = mirror2 (Bin (Bin Leaf Leaf) Leaf) =:= Bin Leaf (Bin Leaf Leaf)

prop_testk :: Prop Tree
prop_testk = mirror2w (Bin (Bin Leaf Leaf) Leaf) =:= Bin Leaf (Bin Leaf Leaf)

prop_testp :: Prop Tree
prop_testp = mirror (Bin (Bin Leaf Leaf) Leaf) =:= Bin Leaf (Bin Leaf Leaf)

prop_testw :: Prop Tree
prop_testw = mirrorw (Bin (Bin Leaf Leaf) Leaf) =:= Bin Leaf (Bin Leaf Leaf)


prop_mirror2fix x    = mirror2fix (mirror2fix x)   =:= x

prop_mirror2wfix x   = mirror2wfix (mirror2wfix x) =:= x

prop_mirror2 x       = mirror2 (mirror2 x)         =:= x

prop_mirror2w x      = mirror2w (mirror2w x)       =:= x

prop_mirror x        = mirror (mirror x)           =:= x

prop_mirrorw x       = mirrorw (mirrorw x)         =:= x

prop_eq_w_ x         = mirrorw x                   =:= mirror x

prop_eq_2_ x         = mirror2 x                   =:= mirror x

prop_eq_2w_w x       = mirror2w x                  =:= mirrorw x

prop_eq_2w_2 x       = mirror2w x                  =:= mirror2 x

prop_eq_2wfix_2fix x = mirror2wfix x               =:= mirror2fix x

prop_eq_2wfix_ x     = mirror2wfix x               =:= mirror x

prop_eq_2fix_w x     = mirror2wfix x               =:= mirrorw x

prop_eq_2wfix_w x    = mirror2wfix x               =:= mirrorw x

prop_eq_2fix_ x      = mirror2 x                   =:= mirror x


