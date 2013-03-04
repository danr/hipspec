{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.ApproximationLemma(approximate) where

import HipSpec.Trans.Obligation
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop
import HipSpec.Trans.Types
import HipSpec.Trans.TypeGuards
import HipSpec.Params

import Control.Concurrent.STM.Promise.Tree

import Halo.FOL.Abstract hiding (Term)
import Halo.Monad
import Halo.Util
import Halo.Shared
import Halo.Subtheory

import Data.Maybe (mapMaybe)

import Control.Monad.Reader
import Control.Monad.State

import qualified CoreSyn as C
import CoreSyn (CoreExpr)
import CoreSubst
import UniqSupply
import DataCon
import Type
import Var
import qualified Outputable as Outputable
import Induction.Structural hiding (Obligation)
import qualified Induction.Structural as IS

import HipSpec.Trans.MakerMonad
import HipSpec.Trans.Literal

approximate :: forall eq . Property eq -> MakerM (Int,Property eq,Property eq)
approximate prop@Property{..} = undefined

{- the idea is if we have

    C => e1 = e2

   make a new variable y and prove

    C & y = e1 => y = e2

   and

    C & y = e2 => y = e1

-}




