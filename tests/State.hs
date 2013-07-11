module State where

import Prelude ()

fst (x,y) = x
snd (x,y) = y

type State s a = s -> (a,s)

bind2 :: State s a -> (a -> State s b) -> State s b
(m `bind2` f) s = let a  = fst (m s)
                      s' = snd (m s)
                  in  f a s'

bind3 :: State s a -> (a -> State s b) -> State s b
(m `bind3` f) s = let (a,s') = m s
                  in  f a s'

bind4 :: State s a -> (a -> State s b) -> State s b
(m `bind4` f) s = let ~(a,s') = m s
                  in  f a s'
