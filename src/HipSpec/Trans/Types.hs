{-# LANGUAGE ViewPatterns,PatternGuards #-}
{-

    Getting Types from GHC to use with induction

    Functions to consider:

      * Looking through type synonyms

        @coreView :: Type -> Maybe Type@
        @tcView   :: Type -> Maybe Type@

-}
module HipSpec.Trans.Types (tyEnv,Bottom(..)) where

import Halo.Util

import Induction.Structural

import Type
import DataCon
import TyCon

import Data.Function (on)

newtype Bottom = Bottom { bottomType :: Type }

instance Eq Bottom where
  (==) = eqType `on` bottomType

instance Ord Bottom where
  compare = cmpType `on` bottomType

-- | Type environment for structural induction
--   Right Type means bottom at this particular type
tyEnv :: Bool -> TyEnv (Either DataCon Bottom) Type
tyEnv add_bottom ty
    | isAlgType ty = fmap add_bottom_con $ Just
                   $ map (first Left)
                   $ uncurry instTyCon (splitTyConApp ty)
    | otherwise    = Nothing
  where
    add_bottom_con
        | add_bottom = ((Right (Bottom ty),[]):)
        | otherwise  = id

-- | Instantiates a TyCon with its type arguments, e.g.
--   List Nat returns [(Nil,[]),(Cons,[NonRec Nat,Rec (List Nat)])]
instTyCon :: TyCon -> [Type] -> [(DataCon,[Arg Type])]
instTyCon ty_con args =
    let cons          :: [DataCon]
        cons          = tyConDataCons ty_con

    in  map (\con -> (con,instDataCon con args)) cons

-- | Instantiates a data constructor to some arguments
instDataCon :: DataCon -> [Type] -> [Arg Type]
instDataCon dc args =
   let parent_ty_con :: TyCon
       parent_ty_con = dataConTyCon dc

       inst_args :: [Type]
       inst_args = dataConInstArgTys dc args

       calc_Arg :: Type -> Arg Type
       calc_Arg ty -- used to be a repType here but we cannot look through newtypes now!
           | Just (ty_con,_) <- splitTyConApp_maybe ty
           , not (isNewTyCon ty_con) -- newtypes are abstract: cannot induct over them
           , ty_con == parent_ty_con = Rec ty

           | isFunTy ty              = Exp ty (fst (splitFunTys ty))

           | otherwise               = NonRec ty

   in  map calc_Arg inst_args

