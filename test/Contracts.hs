{-# LANGUAGE GADTs, KindSignatures, RankNTypes #-}
module Contracts where

data Contract :: * -> * where
  (:->) :: Contract a -> (a -> Contract b) -> Contract (a -> b)
  Pred  :: (a -> Bool) -> Contract a
  CFAnd :: (a -> Bool) -> Contract a
  CF    :: Contract a

{-
{-# INLINEABLE (-->) #-}
(-->) :: Contract a -> Contract b -> Contract (a -> b)
a --> b = a :-> \_ -> b
-}

infix 0 `For`

data Statement = forall a . Contract a `For` a
