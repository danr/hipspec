{-# LANGUAGE ExistentialQuantification #-}
module Zeno (
  Bool (..), Equals (..), Prop,
  prove, proveBool, given, givenBool,
  ($), otherwise
) where
 
import Prelude ( Bool (..) )
 
infix 1 :=:
infixr 0 $
 
($) :: (a -> b) -> a -> b
f $ x = f x
 
otherwise :: Bool
otherwise = True
 
data Equals
  = forall a . (:=:) a a
 
data Prop
  = Given Equals Prop           
  | Prove Equals
 
prove :: Equals -> Prop
prove = Prove
 
given :: Equals -> Prop -> Prop
given = Given
 
proveBool :: Bool -> Prop
proveBool p = Prove (p :=: True)
 
givenBool :: Bool -> Prop -> Prop
givenBool p = Given (p :=: True)

