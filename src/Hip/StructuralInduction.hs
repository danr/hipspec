{-# LANGUAGE PatternGuards, DeriveDataTypeable, ParallelListComp,
             ConstraintKinds, ScopedTypeVariables #-}
{-

   Structural Induction - the heart of HipSpec

-}
module Hip.StructuralInduction
       (Term(..)
       ,Formula(..)
       ,V
       ,TermV
       ,FormulaV
       ,unV
       ,unVM
       ,Arg(..)
       ,TyEnv
       ,structuralInduction
       ,consequent
       ) where

import Control.Arrow hiding ((<+>))
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Data.Generics.Uniplate.Data

import Data.Data
import Data.List
import Data.Maybe

import Hip.Util (concatMapM,nubSorted)

import Safe

type DataOrds c v t = (Ord c,Ord v,Ord t,Data c,Data v,Data t)


-- Terms ----------------------------------------------------------------------

data Term c v = Var v
              | Con c [Term c v]
              | Fun v [Term c v]
              -- ^ Exponentials yield function application
  deriving (Eq,Ord,Show,Data,Typeable)

-- Formulae -------------------------------------------------------------------

data Formula c v t = Forall [(v,t)] (Formula c v t)
                   | [Formula c v t] :=> Formula c v t
                   | P [Term c v]
                   -- ^ The actual predicate that we are doing induction on
  deriving (Eq,Ord,Show,Data,Typeable)

-- | Implication, but with some tidying and simplification
(==>) :: DataOrds c v t => [Formula c v t] -> Formula c v t -> Formula c v t
xs ==> (ys :=> x) = (xs ++ ys) ==> x
xs ==> x          = case tidy xs of
                         [] -> x
                         ts -> ts :=> x
  where
    tidy = nubSorted . filter (not . isAtom)

    isAtom (P tm) = all isAtomTm tm
    isAtom _      = False

    isAtomTm (Con _ tms) = all isAtomTm tms
    isAtomTm _           = False

-- | Tears apart (φs :=> ψ) to (φs,ψ).
unImpl :: Formula c v t -> ([Formula c v t],Formula c v t)
unImpl (phis :=> psi) = (phis,psi)
unImpl psi            = ([],  psi)

-- | Smart creation of foralls
forall' :: DataOrds c v t => [(v,t)] -> Formula c v t -> Formula c v t
forall' xs (Forall ys phi) = forall' (xs ++ ys) phi
forall' xs phi             = case [ (x,t) | (x,t) <- xs, x `varFree` phi ] of
                                []  -> phi
                                xs' -> Forall xs' phi

-- | Does this variable occur in this formula?
varFree :: forall c v t . DataOrds c v t => v -> Formula c v t -> Bool
varFree v phi = or $ [ v == v' | Var v' :: Term c v <- universeBi phi ]
                  ++ [ v == v' | Fun v' _ :: Term c v <- universeBi phi ]

-- | Delete a varibal efrom a type environment
mdelete :: Eq a => a -> [(a,b)] -> [(a,b)]
mdelete x = filter (\(y,_) -> x /= y)

-- Substitution ---------------------------------------------------------------

-- | Substitution on many variables.
--   The rhs of the substitution must be only fresh variables.
substList :: DataOrds c v t => [(v,Term c v)] -> Formula c v t -> Formula c v t
substList subs = transformBi $ \ tm ->
    case tm of
        Var x | Just tm' <- lookup x subs -> tm'
        _                                 -> tm

-- | Substitution. The rhs of the substitution must be only fresh variables.
subst :: DataOrds c v t => v -> Term c v -> Formula c v t -> Formula c v t
subst x t = substList [(x,t)]

-- Arguments ------------------------------------------------------------------

{-| An argument to a constructor can be recursive or non-recursive.

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
-}
data Arg t = Rec t
           | NonRec t
           | Exp t [t]
  deriving (Eq,Ord,Show)

-- | Get the representation of the argument
argRepr :: Arg t -> t
argRepr (Rec t)    = t
argRepr (NonRec t) = t
argRepr (Exp t _)  = t

-- Fresh variables ------------------------------------------------------------

-- | A monad of fresh Integers
type Fresh = State Integer

-- | Cheap way of book-keeping fresh variables
type V v = (v,Integer)

-- | Formulas with fresh-tagged variables
type FormulaV c v t = Formula c (V v) t

-- | Terms with fresh-tagged variables
type TermV c v = Term c (V v)
-- | Create a new fresh variable

newFresh :: v -> Fresh (V v)
newFresh v = do
    x <- get
    modify succ
    return (v,x)

-- | Create a fresh variable that has a type
newTyped :: v -> t -> Fresh (V v,t)
newTyped v t = flip (,) t <$> newFresh v

-- | Refresh variable
newFreshV :: V v -> Fresh (V v)
newFreshV (v,_) = newFresh v

-- | Refresh a variable that has a type
newTypedV :: V v -> t -> Fresh (V v,t)
newTypedV v t = flip (,) t <$> newFreshV v

-- | Flattens out fresh variable names, in a monad
unVM :: Monad m => (v -> Integer -> m v) -> FormulaV c v t -> m (Formula c v t)
unVM f = go
  where
    go phi = case phi of
        Forall xs psi -> liftM2 Forall (forM xs $ \(x,t) -> liftM (flip (,) t)
                                                                  (uncurry f x))
                                       (go psi)
        xs :=> x      -> liftM2 (:=>) (mapM go xs) (go x)
        P xs          -> liftM P (mapM go' xs)

    go' tm = case tm of
        Var x     -> liftM Var (uncurry f x)
        Con c tms -> liftM (Con c) (mapM go' tms)
        Fun x tms -> liftM2 Fun (uncurry f x) (mapM go' tms)

-- | Flattens out fresh variable names
unV :: (v -> Integer -> v) -> FormulaV c v t -> Formula c v t
unV f = runIdentity . unVM (return .: f)

-- Induction ------------------------------------------------------------------

{-| Induction on a variable, given one constructor and the type of
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
-}
indCon :: DataOrds c v t
       => FormulaV c v t -> V v -> c -> [Arg t] -> Fresh (FormulaV c v t)
indCon (Forall qs formula) x con arg_types = do

   let (phis_tmp,psi) = unImpl formula

       (phis,gamma) = partition (varFree x) phis_tmp

       xs = mdelete x qs

   xs' <- mapM (uncurry newTypedV) (mdelete x qs)

   let (psi':phis') = [ substList [(v,Var v') | (v,_) <- xs | (v',_) <- xs' ] f
                      | f <- psi:phis
                      ]

   x1xn_args <- mapM (newTypedV x) arg_types

   let x1xn = map fst x1xn_args

   antecedents <- catMaybes <$> sequence
                      [ fmap (forall' xs') <$> hypothesis (\t -> subst x t f) xi arg
                      | (xi,arg) <- x1xn_args
                      , f <- psi':phis'
                      ]

   let consequent = substList [(x,Con con (map Var x1xn))] psi

       x1xn_typed = map (second argRepr) x1xn_args

   return (forall' (x1xn_typed ++ xs)
                   ((gamma ++ antecedents) ==> consequent))


indCon _ _ _ _ = error "indCon not on a forall quantifier"


{-

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

    This function returns the hypothesis, given a φ(/x), i.e a formula
    waiting for a substiution

-}
hypothesis :: DataOrds c v t
           => (TermV c v -> FormulaV c v t) -> V v -> Arg t
           -> Fresh (Maybe (FormulaV c v t))
hypothesis phi_slash xi arg = case arg of
   NonRec _        -> return Nothing
   Rec _           -> return (Just (phi_slash (Var xi)))
   Exp _ arg_types -> do
       args_typed <- mapM (newTypedV xi) arg_types
       let phi = phi_slash (Fun xi (map (Var . fst) args_typed))
       return (Just (forall' args_typed phi))

-- | Induction on a variable, given all its constructors and their types
--   Returns a number of clauses to be proved, one for each constructor.
induction :: DataOrds c v t
          => FormulaV c v t -> V v -> [(c,[Arg t])] -> Fresh [FormulaV c v t]
induction phi x cons = sequence [ indCon phi x con arg_types
                                | (con,arg_types) <- cons ]


-- Given a type, returns the constructors and the types of their arguments,
-- and also if the arguments are recursive, non-recursive or exponential (see Arg).
--
-- The function should instantiate type variables.
-- For instance, looking up the type List Nat, should return the constructors
-- Nil with args [], and Cons with args [NonRec Nat,Rec (List Nat)].
--
-- If it is not possible to do induction on this type, return Nothing.
-- Examples are function spaces and type variables.
type TyEnv c t = t -> Maybe [(c,[Arg t])]

-- | Folds and concats in a monad
concatFoldM :: (Functor m, Monad m) => (a -> i -> m [a]) -> a -> [i] -> m [a]
concatFoldM _ a []     = return [a]
concatFoldM k a (x:xs) = do rs <- k a x
                            concatMapM (\r -> concatFoldM k r xs) rs

-- | Induction on a term. When we have picked out an argument to the
--   predicate P, it may just as well be a constructor x : xs, and then
--   we can do induction on x and xs (possibly).
inductionTm :: DataOrds c v t
            => TyEnv c t -> FormulaV c v t -> TermV c v -> Fresh [FormulaV c v t]
inductionTm ty_env phi tm = case tm of
    Var x -> case phi of
                 Forall xs _ -> case lookup x xs of
                                   Just ty -> case ty_env ty of
                                                  Just cons -> induction phi x cons
                                                  Nothing   -> return [phi]
                                   _  -> error "inductionTm: x not in quantifier list xs"
                 _ -> error "inductionTm: x not in non-existent quantifier list"
    Con _ tms -> concatFoldM (inductionTm ty_env) phi tms
    Fun _ _   -> error "inductionTm: cannot do induction on a function"

-- | Get consequents
consequent :: Formula c v t -> [Term c v]
consequent (Forall _ phi) = consequent phi
consequent (_ :=> phi)    = consequent phi
consequent (P tms)        = tms

-- | Gets the n:th argument of P, in the consequent
nthArg :: Int -> Formula c v t -> Term c v
nthArg i phi = atNote "StructuralInduction.nthArg" (consequent phi) i

-- | Induction on the term on the n:th coordinate of the predicate.
inductionNth :: DataOrds c v t
             => TyEnv c t -> FormulaV c v t -> Int -> Fresh [FormulaV c v t]
inductionNth ty_env phi i = inductionTm ty_env phi (nthArg i phi)

-- | Performs repeated lexicographic induction, given the typing environment
--
--     * the constructors and their Arg types, for any type
--
--     * arguments and their types
--
--     * which coordinates to do induction on, in order
structuralInduction :: DataOrds c v t
                    => TyEnv c t
                    -- ^ Constructor typed environment
                    -> [(v,t)]
                    -- ^ The initial arguments and types to P
                    -> [Int]
                    -- ^ The coordinates to do induction on in P, in order
                    -> [FormulaV c v t]
                    -- ^ The set of clauses to prove
structuralInduction ty_env args coordinates = flip evalState 0 $ do

    args_fresh <- mapM (uncurry newTyped) args

    let phi = forall' args_fresh (P (map (Var . fst) args_fresh))

    concatFoldM (inductionNth ty_env) phi coordinates

(.:) = (.) . (.)
