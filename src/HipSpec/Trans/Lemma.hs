{-# LANGUAGE RecordWildCards #-}
module HipSpec.Trans.Lemma (translateLemma) where

import HipSpec.Trans.Literal
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop

import Halo.FOL.Abstract hiding (Term)
import Halo.Monad
import Halo.Shared
import Halo.Subtheory
import Halo.MonoType

import Control.Monad.Reader

translateLemma :: Property eq -> Int -> HaloM HipSpecSubtheory
translateLemma Property{..} lemma_num = local (addQuantVars (map fst propVars)) $ do
    tr_lit <- trLiteral propLiteral
    assums <- mapM trLiteral propAssume
    tr_lem <- foralls varMonoType $ assums ===> tr_lit
    return $ subtheory
        { provides    = Specific (Lemma lemma_num)
        , depends     = map Function propFunDeps
        , description = "Lemma " ++ propRepr ++ " (" ++ show lemma_num ++ ")\n" ++
                        "dependencies: " ++ unwords (map idToStr propFunDeps)
        , formulae    = [tr_lem]
        }

