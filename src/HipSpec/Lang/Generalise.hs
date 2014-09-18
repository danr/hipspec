{-# LANGUAGE RecordWildCards #-}
-- | Try to generalise a function
module HipSpec.Lang.Generalise where

import HipSpec.Lang.Simple
import HipSpec.Id hiding (Case)
import HipSpec.Utils

import Data.List (elemIndex)
import Data.Maybe (isJust)

import Data.Generics.Geniplate

{-

 1) Find branches which is only globals applied to input arguments (not bound in case)

 2) For each one, check if all those arguments are constant in recursive calls
    [check that the function actually is recursive]

 3) For each one that is, remove those arguments and generalise over it.


 snoc xs x = case xs of
   []   -> [x]             -- 1) one case with only x
   y:ys -> y:snoc ys x     -- 2) it is passed constant in all recursive calls

 -- Generalised:

 snoc_gen g xs x = case xs of
   []   -> g
   y:ys -> y:snoc_gen g ys x

 Future variation: Don't require that they are constant in recursive calls,
 just introduce new higher-order functions. Probably needs conjecturing of
 lambdas.

 Later: remove unnecessary arguments

-}

generaliseFunction :: Function Id -> Maybe (Function Id)
generaliseFunction fn = case reverse (takeWhile isJust (iterate (genOnce =<<) (Just fn))) of
  Just x:_:_ -> Just (rmRedundant x)
  _ -> Nothing

rmRedundant :: Eq a => Function a -> Function a
rmRedundant fn@Function{..} = fn
  { fn_body = flip transformBi fn_body $ \ e0 -> case e0 of
      (Gbl f _ ts `App` a1) `App` _a2 `App` a3 | f == fn_name -> (Gbl f ty' ts `App` a1) `App` a3
      _ -> e0
  , fn_type = ty'
  , fn_args = take 1 fn_args ++ drop 2 fn_args
  }
 where
  Forall tvs (t1 `ArrTy` (_t2 `ArrTy` tr)) = fn_type
  ty' = Forall tvs (t1 `ArrTy` tr)

genOnce :: Function Id -> Maybe (Function Id)
genOnce Function{..}
  | null recursiveCalls = Nothing
  | otherwise = case candidates of
      []  -> Nothing
      replace_rhs:_ -> Just $ Function new_name new_ty (new_arg:fn_args) (new_body (replace_rhs new_arg_expr))
       where
        Forall tvs ty = fn_type

        new_name :: Id
        new_name = Generalised fn_name `Derived` 0

        new_ty :: PolyType Id
        new_ty = Forall tvs (ArrTy new_arg_ty ty)

        new_arg :: Id
        new_arg = case fn_args of
          []  -> Generalised fn_name `Derived` 1
          x:_ -> Generalised x `Derived` 0

        new_arg_expr :: Expr Id
        new_arg_expr = Lcl new_arg new_arg_ty

        new_arg_ty :: Type Id
        new_arg_ty = res_ty
         where
          (_,res_ty) = collectArrTy ty

        new_body :: Body Id -> Body Id
        new_body = transformBi $ \ e0 -> case e0 of
          Gbl f _ _ | f == fn_name ->
            Gbl new_name new_ty (map TyVar tvs) `App` new_arg_expr
          _ -> e0
 where
  candidates :: [Expr Id -> Body Id]
  candidates =
    [ hole
    | (rhs@App{..},hole) <- rhss fn_body
    -- ^ Check that it is an app, otherwise it is trivial!
    , let lcls = exprLcls rhs
    , all (`elem` fn_args) lcls -- only introduced at the very top level
    , all constant lcls         -- constant across calls
    ]

  recursiveCalls :: [[Expr Id]]
  recursiveCalls =
    [ args
    | (Gbl f _ _,args) <- bodyCalls fn_body
    , f == fn_name
    ]

  -- The id should be one of the arguments in fn_args
  constant :: Id -> Bool
  constant x = case elemIndex x fn_args of
    Nothing -> True
    Just i -> and
      [ case index args i of
          Just (Lcl y _) -> x == y
          _              -> False
      | args <- recursiveCalls
      ]

rhss :: Body a -> [(Expr a,Expr a -> Body a)]
rhss (Body e) = [(e,Body)]
rhss (Case s alts) =
  [ (rhs,\ e -> Case s (l ++ [(p,ctx e)] ++ r))
  | (l,(p,b),r) <- selections alts
  , (rhs,ctx) <- rhss b
  ]
