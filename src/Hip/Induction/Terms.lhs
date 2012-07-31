
  Terms
  =====

  The heart of Structural Induction
 
> {-# LANGUAGE
>       TemplateHaskell,
>       PatternGuards,
>       ExplicitForAll,
>       MultiParamTypeClasses
>   #-}
 
> module Hip.Induction.Terms ( Term(..), varFree, substList, subst ) where

> import Data.Generics.Geniplate

> data Term c v = Var { termVarName :: v }
>               | Con { termConName :: c , termArgs :: [Term c v] }
>               | Fun { termFunName :: v , termArgs :: [Term c v] }

                ^ Exponential datatypes yield functions

>   deriving (Eq,Ord,Show)

  Geniplate Instances
  ===================

> instanceTransformBi [t| forall c v . (Term c v,Term c v) |]
> instanceUniverseBi  [t| forall c v . (Term c v,Term c v) |]

  Free Variables
  ==============
 
  | Does this variable occur in this term?

> varFree :: Eq v => v -> Term c v -> Bool
> varFree v tm = or $ [ v == v' | Var v'   <- universe tm ]
>                  ++ [ v == v' | Fun v' _ <- universe tm ]

  Substitution
  ============

  | Substitution on many variables.
    The rhs of the substitution must be only fresh variables.

> substList :: Eq v => [(v,Term c v)] -> Term c v -> Term c v
> substList subs = transformBi $ \ tm ->
>     case tm of
>         Var x | Just tm' <- lookup x subs -> tm'
>         _                                 -> tm

  | Substitution. The rhs of the substitution must be only fresh variables.

> subst :: Eq v => v -> Term c v -> Term c v -> Term c v
> subst x t = substList [(x,t)]
