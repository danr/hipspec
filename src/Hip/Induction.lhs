

  Structural Induction
  ====================

 
  The heart of HipSpec


  TODO: Rewrite this using Geniplate
 
 
> {-# LANGUAGE PatternGuards, DeriveDataTypeable, ParallelListComp,
>              ConstraintKinds, ScopedTypeVariables,
>              TypeOperators #-}

> module Hip.Induction
>        (Term(..)   ,TermV
>        ,Hypothesis ,HypothesisV
>        ,IndPart(..),IndPartV
>        ,(:::)
>        ,Arg(..)
>        ,unV
>        ,unVM
>        ,TyEnv
>        ,structuralInduction
>        ) where

> import Control.Arrow hiding ((<+>))
> import Control.Applicative hiding (empty)
> import Control.Monad.State
> import Control.Monad.Identity

> import Data.Generics.Uniplate.Data
> import Data.Data
> import Data.List
> import Data.Maybe

> import Halo.Util (concatFoldM,(.:),nubSortedOn)

> import Safe

  Context of Data and Ord
  -----------------------

> type DataOrds c v = (Data c,Data v,Ord c,Ord v)

  Typed variables
  ===============
 
> type v ::: t = (v,t)

  | Delete a varibale from a type environment

> mdelete :: Eq a => a -> [a ::: b] -> [a ::: b]
> mdelete x = filter (\(y,_) -> x /= y)

  Predicate
  =========

  The abstract predicate P is of some arity, and the arguments are in a list

> type Predicate c v = [Term c v]

  Hypotheses
  ==========

> type Hypothesis c v t = ([v ::: t],Predicate c v)

> quantify :: DataOrds c v => [v ::: t] -> Hypothesis c v t -> Hypothesis c v t
> quantify xs (ys,hyp) = ([(x,t) | (x,t) <- xs, any (x `varFree`) hyp] ++ ys,hyp)

> tidy :: DataOrds c v => [Hypothesis c v t] -> [Hypothesis c v t]
> tidy = nubSortedOn (first (map fst))
>      . filter (not . all isAtom . snd)
>   where
>     isAtom (Con _ tms) = all isAtom tms
>     isAtom _           = False

  Induction steps data type
  =========================

> data IndPart c v t = IndPart { implicit   :: [v ::: t]
>                              , hypotheses :: [Hypothesis c v t]
>                              , conclusion :: Predicate c v
>                              }
>   deriving(Eq,Ord,Show,Data,Typeable)

  Terms
  =====

> data Term c v = Var { termVarName :: v }
>               | Con { termConName :: c , termArgs :: [Term c v] }
>               | Fun { termFunName :: v , termArgs :: [Term c v] }

                ^ Exponential datatypes yield functions

>   deriving (Eq,Ord,Show,Data,Typeable)

  | Does this variable occur in this term?

> varFree :: forall c v . (Data c,Data v,Eq v) => v -> Term c v -> Bool
> varFree v tm = or $ [ v == v' | Var v'   <- universe tm ]
>                  ++ [ v == v' | Fun v' _ <- universe tm ]




  Substitution
  ============

  | Substitution on many variables.
    The rhs of the substitution must be only fresh variables.

> substList :: (Data c,Data v,Eq v) => [(v,Term c v)] -> Term c v -> Term c v
> substList subs = transformBi $ \ tm ->
>     case tm of
>         Var x | Just tm' <- lookup x subs -> tm'
>         _                                 -> tm

  | Substitution. The rhs of the substitution must be only fresh variables.

> subst :: (Data c,Data v,Eq v) => v -> Term c v -> Term c v -> Term c v
> subst x t = substList [(x,t)]

  Arguments
  =========

  An argument to a constructor can be recursive or non-recursive.

  For instance, when doing induction on [a], then (:) has two arguments,
  NonRec a and Rec [a].

  If doing induction on [Nat], then (:) has NonRec Nat and Rec [Nat]

  So Rec signals that there should be emitted an induction hypothesis here.

  Data types can also be exponential. Consider

  @
      data Ord = Zero | Succ Ord | Lim (Nat -> Ord)
  @

  Here, the Lim constructor is exponential, create it with

  @
      Exp (Nat -> Ord) [Nat]
  @

  The first argument is the type of the function, and the second
  argument are the arguments to the function. The apparent duplication
  is there because the type is kept entirely abstract in this module.

> data Arg t = Rec t
>            | NonRec t
>            | Exp t [t]
>   deriving (Eq,Ord,Show)

  Get the representation of the argument

> argRepr :: Arg t -> t
> argRepr (Rec t)    = t
> argRepr (NonRec t) = t
> argRepr (Exp t _)  = t

  Type environment
  ================

  Given a type, returns the constructors and the types of their arguments,
  and also if the arguments are recursive, non-recursive or exponential (see Arg).

  The function should instantiate type variables.
  For instance, looking up the type List Nat, should return the constructors
  Nil with args [], and Cons with args [NonRec Nat,Rec (List Nat)].

  If it is not possible to do induction on this type, return Nothing.
  Examples are function spaces and type variables.

> type TyEnv c t = t -> Maybe [c ::: [Arg t]]

  Fresh variables
  ===============

  A monad of fresh Integers

> type Fresh = State Integer

  Cheap way of introducing fresh variables

> type V v = (v,Integer)

  Our datatypes with tagged variables

> type IndPartV c v t = IndPart c (V v) t
> type TermV c v = Term c (V v)
> type HypothesisV c v t = Hypothesis c (V v) t

  Creating a fresh variable

> newFresh :: v -> Fresh (V v)
> newFresh v = do
>     x <- get
>     modify succ
>     return (v,x)

  Create a fresh variable that has a type

> newTyped :: v -> t -> Fresh (V v ::: t)
> newTyped v t = flip (,) t <$> newFresh v

  Refresh variable

> refreshV :: V v -> Fresh (V v)
> refreshV (v,_) = newFresh v

  Refresh a variable that has a type

> refreshTypedV :: V v -> t -> Fresh (V v ::: t)
> refreshTypedV v t = flip (,) t <$> refreshV v

  Removing fresh variables
  ------------------------

> -- | Flattens out fresh variable names, in a monad
> unVM :: (Applicative m,Monad m)
>      => (v -> Integer -> m v) -> IndPartV c v t -> m (IndPart c v t)
> unVM f (IndPart skolem hyps concl)
>     = IndPart <$> unQuant skolem
>               <*> mapM (\(qs,hyp) -> (,) <$> unQuant qs <*> mapM unTm hyp) hyps
>               <*> mapM unTm concl
>   where
>     f' = uncurry f
>
>     unQuant = mapM (\(v,t) -> (,) <$> f' v <*> return t)
>
>     unTm tm = case tm of
>         Var x     -> Var <$> f' x
>         Con c tms -> Con c <$> mapM unTm tms
>         Fun x tms -> Fun <$> f' x <*> mapM unTm tms
>
> -- | Flattens out fresh variable names
> unV :: (v -> Integer -> v) -> IndPartV c v t -> IndPart c v t
> unV f = runIdentity . unVM (return .: f)

  Induction
  =========

  Induction on a variable, given one constructor and the type of
  its arguments. We need to make some special care when
  we are doing induction on an implication. Say we have

  @
    ∀ (x,xs) . γ(xs) ∧ φ(x,xs) → ψ(x,xs)
  @

  The γ are properties unrelated to x. These are put away for now.
  We're doing induction on x, it has a constructor C with n
  arguments, let's for simplicitity say that they are all recursive.
  Now, define a temporary P:

  @
    P(x) <=> ∀ xs . φ(x,xs) ∧ ψ(x,xs)
  @

  Notice the conjuction. Induction:

  @
    ∀ (x₁..xₙ) . P(x₁) ∧ ... ∧ P(xₙ)
               → P(C x₁ .. xₙ)
  @

  Unroll P, and move its quantifier in the consequent:

  @
    ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′) ∧ ψ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . φ(xₙ,xs′) ∧ ψ(xₙ,xs′))
                  → φ(C x₁ .. xₙ,xs) ∧ ψ(C x₁ .. xₙ,xs)
  @

  Ok, so we have two proof obligations, φ and ψ. Let us take φ
  first. It turns out that we don't need ψ here, so we strip them:

  @
    ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . φ(xₙ,xs′))
                  → φ(C x₁ .. xₙ,xs)
  @

  And this is true by structural induction! Hooray! So what we are
  left with is this:

  @
    ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′) ∧ ψ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . φ(xₙ,xs′) ∧ ψ(xₙ,xs′))
                  → ψ(C x₁ .. xₙ,xs)
  @

  Since our target language does not have conjuction, we may just as
  well write it as this:

  @
    ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . φ(xₙ,xs′))
                  ∧ (∀ xs′ . ψ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . ψ(xₙ,xs′))
                  → ψ(C x₁ .. xₙ,xs)
  @

  Now, we knew from the start that ∀ xs . γ(xs), se we bring that back:

  @
    ∀ (x1..xn) xs . γ(xs)
                  ∧ (∀ xs′ . φ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . φ(xₙ,xs′))
                  ∧ (∀ xs′ . ψ(x₁,xs′))
                  ∧ ...
                  ∧ (∀ xs′ . ψ(xₙ,xs′))
                  → ψ(C x₁ .. xₙ,xs)
  @

  Then it fits our data type perfectly. We have implicitly
  quantified variables, x1 .. xn and xs, a bunch of hypotheses
  quantifying new variables, and and induction conclusion.

  | Induction on a constructor, given its arguments as above

> indCon :: forall c v t . DataOrds c v
>        => IndPartV c v t -> V v -> c -> [Arg t] -> Fresh (IndPartV c v t)
> indCon (IndPart x_and_xs gamma_and_phi psi) x con arg_types = do
>
>    let phis :: [HypothesisV c v t]
>        (phis,gamma) = partition (any (varFree x) . snd) gamma_and_phi
>
>        xs = mdelete x x_and_xs
>
>    xs' <- mapM (uncurry refreshTypedV) xs
>
>    let (psi':phis') = map (second (map (substList [ (v,Var v')
>                                                   | (v,_) <- xs
>                                                   | (v',_) <- xs' ])))
>                           (([],psi):phis)
>
>
>    x1xn_args <- mapM (refreshTypedV x) arg_types
>
>    let x1xn = map fst x1xn_args
>
>    antecedents <- catMaybes <$> sequence
>                       [ fmap (quantify xs')
>                           <$> hypothesis (\tm -> (qs,map (subst x tm) hyp)) xi arg
>                       | (xi,arg) <- x1xn_args
>                       , (qs,hyp) <- psi':phis'
>                       ]
>
>    let consequent = map (substList [(x,Con con (map Var x1xn))]) psi
>
>        x1xn_typed = map (second argRepr) x1xn_args
>
>    return $ IndPart (x1xn_typed ++ xs)
>                     (tidy $ gamma ++ antecedents)
>                     (consequent)

  In the commentary about indCon we assumed that all arguments were
  recurisive. This is not necessarily so, consider

  @
     (:) : a -> [a] -> [a]
  @

  The first argument is non-recursive, the second is recursive. We
  also have exponentials:

  @
     Lim : (Nat -> Ord) -> Ord
  @

  While while we cannot continue do induction on the function space
  Nat -> Ord, we still get an induction hypothesis:

  @
     ∀ f . (∀ x . P(f(x))) → P(Lim(f))
  @

  To summarise, given the constructor C t₁ .. tₙ and formula

  @
     ∀ (x,xs) . φ(x,xs) → ψ(x,xs)
  @

  yields, when doing induction on x:

  @
     ∀ (x₁:t₁ .. xₙ:tₙ,xs) .

       ⋀ { if tᵢ non-recursive : ∅
           if tᵢ recursive     : { ∀ xs′ . φ(xᵢ,xs′)
                                 , ∀ xs′ . ψ(xᵢ,xs′)
                                 }
           if tᵢ exponential,
           with arguments of type ts : { ∀ xs′ . ∀ (ys : ts) . φ(xᵢ(ys),xs′)
                                       , ∀ xs′ . ∀ (ys : ts) . ψ(xᵢ(ys),xs′)
                                       }
           as a function call on xᵢ with args ys
         | xᵢₖ <- x₁..xₙ
         }

       → ψ(C x₁..xₙ,xs)
  @

  | This function returns the hypothesis, given a φ(/x),
    i.e a hypothesis waiting for a substiution

> hypothesis :: DataOrds c v
>            => (TermV c v -> HypothesisV c v t) -> V v -> Arg t
>            -> Fresh (Maybe (HypothesisV c v t))
> hypothesis phi_slash xi arg = case arg of
>    NonRec _        -> return Nothing
>    Rec _           -> return (Just (phi_slash (Var xi)))
>    Exp _ arg_types -> do
>        args_typed <- mapM (refreshTypedV xi) arg_types
>        let phi = phi_slash (Fun xi (map (Var . fst) args_typed))
>        return (Just (quantify args_typed phi))

  | Induction on a variable, given all its constructors and their types
    Returns a number of clauses to be proved, one for each constructor.

> induction :: DataOrds c v
>           => IndPartV c v t -> V v -> [c ::: [Arg t]] -> Fresh [IndPartV c v t]
> induction phi x cons = sequence [ indCon phi x con arg_types
>                                 | (con,arg_types) <- cons ]

  | Induction on a term. When we have picked out an argument to the
    predicate P, it may just as well be a constructor x : xs, and then
    we can do induction on x and xs (possibly).

> inductionTm :: DataOrds c v
>             => TyEnv c t -> IndPartV c v t -> TermV c v -> Fresh [IndPartV c v t]
> inductionTm ty_env part@(IndPart xs _ _) tm = case tm of
>     Var x -> let ty = lookupJustNote "inductionTm: x not quantified" x xs
>              in  case ty_env ty of
>                      Just cons -> induction part x cons
>                      Nothing   -> return [part]
>     con_or_fun -> concatFoldM (inductionTm ty_env) part (termArgs con_or_fun)

  | Gets the n:th argument of the conclusion, in the consequent

> getNthArg :: Int -> IndPart c v t -> Term c v
> getNthArg i p = atNote "Induction.getNthArg" (conclusion p) i

  | Induction on the term on the n:th coordinate of the predicate.

> inductionNth :: DataOrds c v
>              => TyEnv c t -> IndPartV c v t -> Int -> Fresh [IndPartV c v t]
> inductionNth ty_env phi i = inductionTm ty_env phi (getNthArg i phi)

  | Perform repeated lexicographic induction, given the typing environment

      * the constructors and their Arg types, for any type

      * arguments and their types

      * which coordinates to do induction on, in order

> structuralInduction :: DataOrds c v
>                     => TyEnv c t
>                     -- ^ Constructor typed environment
>                     -> [(v,t)]
>                     -- ^ The initial arguments and types to P
>                     -> [Int]
>                     -- ^ The coordinates to do induction on in P, in order
>                     -> [IndPartV c v t]
>                     -- ^ The set of clauses to prove
> structuralInduction ty_env args coordinates = flip evalState 0 $ do
>
>     args_fresh <- mapM (uncurry newTyped) args
>
>     let init_part = IndPart args_fresh [] (map (Var . fst) args_fresh)
>
>     concatFoldM (inductionNth ty_env) init_part coordinates

