module State where

import Prelude ()

type State s a = s -> (a,s)

fst (a,b) = a
snd (a,b) = b

(>>=) :: State s a -> (a -> State s b) -> State s b
m >>= f = \s -> let a  = fst (m s)
                    s' = snd (m s)
                in  f a s'


(>>==) :: State s a -> (a -> State s b) -> State s b
(m >>== f) s = let a  = fst (m s)
                      s' = snd (m s)
                  in  f a s'

