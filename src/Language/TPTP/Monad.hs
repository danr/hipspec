{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
                                TypeSynonymInstances #-}
module Language.TPTP.Monad (module Language.TPTP
                           ,M
                           ,run
                           ,newVar
                           ,constant
                           ,unary
                           ,binary
                           ,trinary
                           ,predicate
                           ,relation
                           ,trinaryRel
                           ,(==>),(&),(/\),(\/),(<=>)
                           ,(===),(!=)
                           ,axiom
                           ,conjecture
                           ,question
                           ,hypothesis
                           ,definition
                           ,lemma
                           ,forall'
                           ,exists'
                           ,neg
                           ) where

import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad
import Control.Monad.State
import Control.Applicative hiding (empty)
import Control.Arrow (first,second,(***))

import Language.TPTP hiding ((===),(!=),(&),(/\),(\/),(==>),(<=>)
                            ,mkBinOp,forall',exists')

type ST = [VarName]

newtype M a = M { runM :: State ST a }
  deriving (Monad,MonadState ST,Functor,Applicative)

run :: M a -> a
run m = evalState (runM m) vars
  where vars = map VarName ((`replicateM` "XYZUVW") =<< [1..]) -- [ VarName ("X" ++ show x) | x <- [0..] ]

newVar :: M VarName
newVar = do
  v:vs <- get
  put vs
  return v

constant :: String -> M Term
constant n = return (Fun (FunName n) [])

unary :: String -> M Term -> M Term
unary n = liftM (Fun (FunName n) . pure)

binary :: String -> M Term -> M Term -> M Term
binary n = liftM2 (\x y -> Fun (FunName n) [x,y])

trinary :: String -> M Term -> M Term -> M Term -> M Term
trinary n = liftM3 (\x y z -> Fun (FunName n) [x,y,z])

predicate :: String -> M Term -> M Formula
predicate n = liftM (Rel (RelName n) . pure)

relation :: String -> M Term -> M Term -> M Formula
relation n = liftM2 (\x y -> Rel (RelName n) [x,y])

trinaryRel :: String -> M Term -> M Term -> M Term -> M Formula
trinaryRel n = liftM3 (\x y z -> Rel (RelName n) [x,y,z])

mkBinOp :: BinOp
        -> M Formula -> M Formula -> M Formula
mkBinOp op = liftM2 (\f g -> BinOp f op g)

infix 4 ===
infix 4 !=
infixr 3 &
infixr 3 /\
infixr 2 \/
infixl 1 ==>
infix  1 <=>

(==>) = mkBinOp (:=>)
(&)   = mkBinOp (:&)
(/\)  = mkBinOp (:&)
(\/)  = mkBinOp (:|)
(<=>) = mkBinOp (:<=>)

(===),(!=) :: M Term -> M Term -> M Formula
(===) = liftM2 (\f g -> EqOp f (:==) g)
(!=)  = liftM2 (\f g -> EqOp f (:!=) g)

neg :: M Formula -> M Formula
neg = fmap Neg

axiom :: String -> M Formula -> Decl
axiom s f = Axiom s (run f)

conjecture :: String -> M Formula -> Decl
conjecture s f = Conjecture s (run f)

question :: String -> M Formula -> Decl
question s f = Question s (run f)

lemma :: String -> M Formula -> Decl
lemma s f = Lemma s (run f)

hypothesis :: String -> M Formula -> Decl
hypothesis s f = Hypothesis s (run f)

definition :: String -> M Formula -> Decl
definition s f = Definition s (run f)


class Quantifier t where
    quantifier
        :: ([VarName] -> Formula -> Formula) -- ^ quantifier, Forall or Exists
        -> [VarName]                         -- ^ accumulated used variables
        -> t                                 -- ^ Formula or (Term -> t)
        -> M Formula                         -- ^ resulting formula

instance Quantifier (M Formula) where
    quantifier q acc f = q (reverse acc) <$> f

instance Quantifier r => Quantifier (M Term -> r) where
    quantifier q acc f = newVar >>= \v -> quantifier q (v:acc)
                                                     (f (return (Var v)))

forall' :: (Quantifier t) => t -> M Formula
forall' = quantifier Forall []

exists' :: (Quantifier t) => t -> M Formula
exists' = quantifier Exists []

