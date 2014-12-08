{-# LANGUAGE RecordWildCards #-}
module HipSpec.Translate where

import HipSpec.Theory

import qualified HipSpec.Lang.Rich as R
--import HipSpec.Lang.Rich (Datatype(..),Constructor(..))

import HipSpec.Lang.CoreToRich as CTR
import HipSpec.Lang.RichToSimple
import HipSpec.Lang.CollapseSimp

import HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.FunctionalFO as FO

import HipSpec.Lang.SimpleToFO as FO
import HipSpec.Lang.Deappify

import qualified HipSpec.Lang.ToPolyFOL as P
import qualified HipSpec.Lang.PolyFOL as P

--import Name
import CoreSyn (CoreExpr)

import qualified Data.Map as M
import qualified Data.Set as S

import Var (Var)

import TyCon (TyCon,isNewTyCon,tyConUnique)
import qualified PrelNames
import qualified TysPrim
import qualified TysWiredIn

import Control.Monad

import Induction.Structural

import HipSpec.Id

appThy :: Subtheory
appThy = Subtheory
    { defines = AppThy
    , clauses = P.appAxioms
    , deps    = S.empty
    }

-- | The type environment for induction.
--   Constructors are typed, to know which types has been applied to them
--   We also need to know the full type of the constructor to be able to put it
--   in typed expressions
type Con    = (Id,PolyType Id,[Type Id])
type TyEnv' = TyEnv Con (Type Id)

isAbstract :: TyCon -> Bool
isAbstract tc = isNewTyCon tc || CTR.essentiallyInteger tc

-- | Translates the type constructors
trTyCons :: [TyCon] -> (ArityMap,[Subtheory],TyEnv',[Datatype Id])
trTyCons tcs = case sequence [ fmap ((,) tc) (trTyCon tc) | tc <- tcs ] of
    Right data_types -> (con_arities,subthys,ty_env,map snd data_types)
      where
        subthys = concat
            [ calcDeps subtheory
                  { defines = Type data_ty_con
                  , clauses =
                      if isNewTyCon tc
                          then [ cl | cl@P.SortSig{} <- cls ]
                          else cls
                  }
              : concat
              [ [ Subtheory
                  { defines = Definition dc
                  , clauses = []
                  , deps    = S.singleton (Type data_ty_con)
                  }
                , calcDeps subtheory
                  { defines = Pointer dc
                  , clauses = dc_ptr_cls
                  }
                ]
              | (dc,dc_ptr_cls) <- dc_ptr_clss
              , not (isAbstract tc)
              ]
            | (tc,dt@Datatype{..}) <- data_types
            , let (cls,dc_ptr_clss) = P.trDatatype dt
            ]

        con_arities = M.fromList
            [ (R.con_name dc,length (R.con_args dc))
            | (tc,dt) <- data_types
            , not (isAbstract tc)
            , dc <- data_cons dt
            ]

        m_tcs = M.fromList
            [ (data_ty_con,dt)
            | (tc,dt@Datatype{..}) <- data_types
            , not (isAbstract tc)
            ]

        ty_env :: TyEnv'
        ty_env t0 = do
            TyCon tc tc_args <- return t0
-- -- we would like to have this, but CVC gets all confused:
--          guard (tc `notElem` (map idFromTyCon [TysWiredIn.intTyCon,TysWiredIn.charTyCon]))
            Datatype{..} <- M.lookup tc m_tcs
            return
                [ ( ( con_name
                    , Forall data_tvs
                          (makeArrows con_args (TyCon data_ty_con (map TyVar data_tvs)))
                    , tc_args -- con_args'
                    )
                  , [ case collectArrTy t of
                        (ts,r) | r == t0 -> case ts of
                            [] -> Rec r
                            _  -> Exp t ts
                        _                      -> NonRec t
                    | t <- con_args'
                    ]
                  )
                | Constructor{..} <- data_cons
                , let con_args' = map (substManyTys (zip data_tvs tc_args)) con_args
                ]

    Left err -> error $ "trTyCons: " ++ show err


-- | Translates Var/Expr-pairs to rich functions
toRich :: [(Var,CoreExpr)] -> [R.Function Id]
toRich = map (uncurry to_rich)
  where
    to_rich v e = case runTM (trDefn v e) of
        Right fn -> fn
        Left err -> error $ "toRich: " ++ show err

toSimp :: [R.Function Id] -> [S.Function Id]
toSimp = collapseSimp . uncurry (++) . runRTS . mapM rtsFun

-- | Translates a bunch of simple functions into subtheories
trSimpFuns :: ArityMap -> [S.Function Id] -> (ArityMap,[Subtheory])
trSimpFuns am simp_fns = (new_arities,subthys)
  where
    fo_fns :: [FO.Function Id]
    fo_fns = map stfFun simp_fns

    new_arities :: ArityMap
    new_arities = M.fromList
        [ (fn_name,length fn_args) | FO.Function{..} <- fo_fns ]

    fo_fns_zapped :: [FO.Function Id]
    fo_fns_zapped = mapM zapFn fo_fns (`M.lookup` am)

    subthys = concat
        [ [ calcDeps subtheory
            { defines = Definition fn_name
            , clauses = fn_cls
            }
          , calcDeps subtheory
            { defines = Pointer fn_name
            , clauses = ptr_cls
            }
          ]
        | f@FO.Function{..} <- fo_fns_zapped
        , let (fn_cls,ptr_cls) = P.trFun f
        ]

trSimpExpr :: ArityMap -> [Id] -> S.Expr Id -> P.Term LogicId LogicId
trSimpExpr am sc e = P.trExpr' sc (stfExpr e `zapExpr` (`M.lookup` am))

