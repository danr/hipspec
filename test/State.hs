module State where

import Prelude ()

type State s a = s -> T a s

data T a b = T a b

fst (T a b) = a
snd (T a b) = b

bind :: State s a -> (a -> State s b) -> State s b
m `bind` f = \s -> let a  = fst (m s)
                       s' = snd (m s)
                    in  f a s'


-- bind2 :: State s a -> (a -> State s b) -> State s b
-- (m `bind2` f) s = let a  = fst (m s)
--                       s' = snd (m s)
--                   in  f a s'

-- These fail with no support of let statements
-- bind3 :: State s a -> (a -> State s b) -> State s b
-- (m `bind3` f) s = let ~(T a s') = m s
--                   in  f a s'

--  bind4 :: State s a -> (a -> State s b) -> State s b
--  (m `bind4` f) s = let T a s' = m s
--                    in  f a s'

