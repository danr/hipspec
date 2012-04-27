module Lists where

import Prelude (Bool(..))

{-

insert_sba [Occ=LoopBreaker]
  :: forall t_aan.
     (t_aan -> t_aan -> GHC.Types.Bool) -> t_aan -> [t_aan] -> [t_aan]
[LclId,
 Arity=3,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=IF_ARGS [60 0 40] 150 360}]
insert_sba =
  \ (@ t_aan)
    (<_a9N :: t_aan -> t_aan -> GHC.Types.Bool)
    (x_a9O :: t_aan)
    (ds_daX :: [t_aan]) ->
    case ds_daX of _ {
      [] -> GHC.Types.: @ t_aan x_a9O (GHC.Types.[] @ t_aan);
      : y_a9R ys_a9S ->
        case <_a9N x_a9O y_a9R of _ {
          GHC.Types.False ->
            GHC.Types.: @ t_aan y_a9R (insert_sba @ t_aan <_a9N x_a9O ys_a9S);
          GHC.Types.True ->
            GHC.Types.: @ t_aan x_a9O (GHC.Types.: @ t_aan y_a9R ys_a9S)
        }
    };

Lists.insert
  :: forall t_aal.
     (t_aal -> t_aal -> GHC.Types.Bool) -> t_aal -> [t_aal] -> [t_aal]
[LclIdX,
 Arity=3,
 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Lists.insert = \ (@ t_aan) -> insert_sba @ t_aan

           -- ^ Here is a copy of the function =l
           --   Messes up the simple pretty printing we have right
           --   now, making a clash. Ideally, I would not like to see
           --   this extra function.

-}

otherwise = True

insert (<) x [] = [x]
insert (<) x (y:ys) | x < y     = x:y:ys
                    | otherwise = y:insert (<) x ys

isort (<) [] = []
isort (<) (x:xs) = insert (<) x (isort (<) xs)

swap [x,y] = [y,x]
rot [x,y,z] = [z,x,y]