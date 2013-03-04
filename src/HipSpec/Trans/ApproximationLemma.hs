{-# LANGUAGE RecordWildCards,NamedFieldPuns,TypeOperators,
             ParallelListComp,ViewPatterns,ScopedTypeVariables #-}
module HipSpec.Trans.ApproximationLemma(approximate) where

approximate :: forall eq . Property eq -> Maybe (MakerM (Int,Property eq,Property eq))
approximate prop@Property{..}


