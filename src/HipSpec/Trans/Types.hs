{-# LANGUAGE ViewPatterns,PatternGuards #-}
{-

    Getting Types from GHC to use with induction

    Functions to consider:

      * Looking through type synonyms

        @coreView :: Type -> Maybe Type@
        @tcView   :: Type -> Maybe Type@

-}
module HipSpec.Trans.Types
    ( tyEnv
    , finiteType
    ) where


import Halo.Shared

import HipSpec.Induction

import Type
import DataCon
import TyCon hiding (data_con)
import Outputable
import TysWiredIn
import TysPrim
import BasicTypes

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
       calc_Arg (repType' -> ty)
           | Just (ty_con,_) <- splitTyConApp_maybe ty
           , ty_con == parent_ty_con = Rec ty

           | isFunTy ty              = Exp ty (fst (splitFunTys ty))

           | otherwise               = NonRec ty

   in  map calc_Arg inst_args

-- | Is this type definitely finite?
--
--   Examples: (), Bool, Ordering, Either Bool Bool, Maybe (), ...
--
--   Counterexamples: [()], [Bool], [a], Either a Bool, m a ...
finiteType :: Type -> Bool
finiteType ty = finType [] ty
  where
    --
    finType :: [Type] -> Type -> Bool
    finType visited (repType' -> ty)    -- repType' looks through foralls,
                                        -- synonyms, predicates and newtypes

        -- Recursive types are never finite
        | any (eqType ty) visited = False

        -- Check that arguments to all constructors are finite
        | isAlgType ty =
             let (ty_con,args) = splitTyConApp ty

                 cons :: [DataCon]
                 cons = tyConDataCons ty_con

             in  all (finType visited')
                     (concatMap (\con -> dataConInstArgTys con args) cons)

        -- If a and b are finite, then a -> b is too.
        -- TODO: if b is singleton (or empty) then this is also finite
        --       (1 or 0 inhabitants)
        | isFunTy ty =
             let (args,res) = splitFunTys ty
             in  all (finType visited') (res:args)

        -- Type variable types are not always finite
        | isTyVarTy ty = False

        -- Something applied to a type variable is not always finite
        | Just (t1,_) <- splitAppTy_maybe ty = isTyVarTy t1

        -- GHC.Prim.Any is not finite
        | ty `eqType` anyTy = False

        -- Raise error if we get some other type
        | otherwise    = error $ "HipSpec.Trans.Types.finiteType "
                              ++ showOutputable ty
                              ++ " neither forall, alg, fun or type variable!"
      where
        visited' = ty:visited

-- | Finite types
true :: [Type]
true = [ boolTy
       , unitTy
       , boolTy `mkFunTy` boolTy
       , mkTupleTy UnboxedTuple [boolTy,boolTy]
       , mkTupleTy UnboxedTuple [boolTy,boolTy] `mkFunTy`
             mkTupleTy UnboxedTuple [unitTy,unitTy,boolTy `mkFunTy` boolTy]
       ]

-- | Infinite types
false :: [Type]
false = [ mkListTy boolTy
        , mkListTy unitTy
        , mkListTy boolTy `mkFunTy` boolTy
        , mkTupleTy UnboxedTuple [boolTy,boolTy] `mkFunTy`
              mkTupleTy UnboxedTuple [unitTy,mkListTy boolTy,boolTy `mkFunTy` boolTy]
        , mkTyVarTy undefined
        , mkListTy (mkTyVarTy undefined)
        ]

-- | Should give all True
unitTests :: [Bool]
unitTests = [ finiteType ty       | ty <- true ]
         ++ [ not (finiteType ty) | ty <- false ]

