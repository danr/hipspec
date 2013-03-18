TODO
====

  * Perform eta-expansion of properties.

  * Change STM-promise:

        (Property :|> Method :&> Leaf Obligation)

    to
        (Property :|> Method :&> Obligation :|> Leaf Prover)

    where

        data (u :|> v) a = Or u [v a]

        data (u :&> v) a = And u [v a]

        data Leaf u a = Leaf u a

        data (u :?> v) a = Par u [v a]      (for as many as possible/recoverable)

        class Exec u a | u -> a where
            exec :: u (Promise a) -> IO (u (PromiseResult a))

        instance Exec (Leaf u a) a where
            ...

        instance Exec v a => Exec (u :|> v) a where
            ...

    And some function change the leaves (add new theorem provers in the end)

    This might be nice. What do I know?


