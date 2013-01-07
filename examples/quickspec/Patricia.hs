data PatriciaTrieR a = Tip a
                     | Arm Bool (PatriciaTrieR a)
                     | Branch (PatriciaTrieR a) (PatriciaTrieR a)

data Maybe a = Just a | Nothing

type PatriciaTrie a = Maybe (PatriciaTrieR a)

type BVec = [Bool]

singletonR :: {n : ℕ} -> BVec n -> A -> PatriciaTrieR n
singletonR []       a = Tip a
singletonR (x ∷ xs) a = Arm x (singletonR xs a)

singleton :: BVec -> a -> PatriciaTrie a
singleton xs a = just (singletonR xs a)

getR ::  BVec n -> PatriciaTrieR n -> Maybe A
getR []       (Tip a)   = just a
getR (x ∷ xs) (Arm b t) with x ≟ b
... | yes p = getR xs t
... | no ¬p = nothing
getR (true ∷ xs)  (Branch l r) = getR xs r
getR (false ∷ xs) (Branch l r) = getR xs l

get : {n : ℕ} -> BVec n -> PatriciaTrie n -> Maybe A
get xs nothing  = nothing
get xs (just t) = getR xs t

setR : {n : ℕ} -> BVec n -> PatriciaTrieR n -> Maybe A -> PatriciaTrie n
setR []       (Tip a)      m = Tip <$> m
setR (x ∷ xs) (Arm b t)    m with cmp x b | m
... | tri< _ _ _ | nothing = just (Arm b t)
... | tri< _ _ _ | just a  = just (Branch (singletonR xs a) t)
... | tri≈ _ _ _ | _       = Arm b <$> setR xs t m
... | tri> _ _ _ | nothing = just (Arm b t)
... | tri> _ _ _ | just a  = just (Branch t (singletonR xs a))
setR (true ∷ xs)  (Branch l r) m with setR xs r m
... | nothing = just (Arm false l)
... | just r′ = just (Branch l r′)
setR (false ∷ xs) (Branch l r) m with setR xs l m
... | nothing = just (Arm true r)
... | just l′ = just (Branch l′ r)

set : {n : ℕ} -> BVec n -> PatriciaTrie n -> Maybe A -> PatriciaTrie n
set xs (just t) m = setR xs t m
set xs nothing  m = singletonR xs <$> m

