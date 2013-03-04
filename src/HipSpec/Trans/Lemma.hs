{-# LANGUAGE RecordWildCards #-}
module HipSpec.Trans.Lemma (translateLemma) where

import HipSpec.Trans.Literal
import HipSpec.Trans.Theory
import HipSpec.Trans.Property as Prop

import Halo.FOL.Abstract hiding (Term)
import Halo.Monad
import Halo.Shared
import Halo.Subtheory

import Control.Monad.Reader

translateLemma :: Property eq -> Int -> HaloM HipSpecSubtheory
translateLemma Property{..} lemma_num = do
    (tr_lem,ptrs) <- capturePtrs equals
    return $ Subtheory
        { provides    = Specific (Lemma lemma_num)
        , depends     = map Function propFunDeps ++ ptrs
        , description = "Lemma " ++ propRepr ++ " (" ++ show lemma_num ++ ")\n" ++
                        "dependencies: " ++ unwords (map idToStr propFunDeps)
        , formulae    = [tr_lem]
        }
  where
    equals :: HaloM Formula'
    equals = do
        (tr_lit,lit_mins) <- trLiteral propLiteral
        (assums,_) <- mapAndUnzipM trLiteral propAssume
        return $ foralls $ ors (map min' lit_mins) ==> (assums ===> tr_lit)


