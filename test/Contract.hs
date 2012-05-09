{-# LANGUAGE GADTs, KindSignatures, RankNTypes #-}
module Contract where

import Contracts

data Nat = Zero | Succ Nat

eq :: Nat -> Nat -> Bool
eq Zero Zero = True
eq (Succ n) (Succ m) = eq n m
eq _ _ = False

idNat :: Nat -> Nat
idNat x = x

contr_idNat :: Statement
contr_idNat = (CF :-> \x -> CFAnd (\y -> eq x y)) `For` idNat
--           $[contr| idNat ::: ( x ) -> ( y | eq x y )]

contr_eq :: Statement
contr_eq = (CF :-> \_ -> CF :-> \_ -> CF) `For` eq
--           $[contr| eq ::: CF -> CF -> CF ]

