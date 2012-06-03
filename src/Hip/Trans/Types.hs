{-# LANGUAGE ViewPatterns,PatternGuards #-}
{-|

    Getting Types from GHC to use with induction

    Functions to consider:

      * Looking through type synonyms

        @coreView :: Type -> Maybe Type@
        @tcView   :: Type -> Maybe Type@

-}
module Hip.Trans.Types (tyEnv) where

import Hip.Induction

import Type
import DataCon
import TyCon hiding (data_con)

-- | Type environment for structural induction
tyEnv :: TyEnv DataCon Type
tyEnv ty | isAlgType ty = Just (uncurry instTyCon $ splitTyConApp ty)
         | otherwise    = Nothing

-- | Instantiates a TyCon with its type arguments, e.g.
--   List Nat returns [(Nil,[]),(Cons,[NonRec Nat,Rec (List Nat)])]
instTyCon :: TyCon -> [Type] -> [(DataCon,[Arg Type])]
instTyCon ty_con args =
    let cons          :: [DataCon]
        cons          = tyConDataCons ty_con

    in  map (\con -> (con,instDataCon con args)) cons

-- | Instantiates a data constructor to some arguments
instDataCon :: DataCon -> [Type] -> [Arg Type]
instDataCon data_con args =
   let parent_ty_con :: TyCon
       parent_ty_con = dataConTyCon data_con

       inst_args :: [Type]
       inst_args = dataConInstArgTys data_con args

       calc_Arg :: Type -> Arg Type
       calc_Arg (dropForAlls -> ty)
           | Just (ty_con,_) <- splitTyConApp_maybe ty
           , ty_con == parent_ty_con = Rec ty

           | isFunTy ty              = Exp ty (fst (splitFunTys ty))

           | otherwise               = NonRec ty

   in  map calc_Arg inst_args

