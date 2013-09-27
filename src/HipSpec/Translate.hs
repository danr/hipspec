{-# LANGUAGE RecordWildCards #-}
module HipSpec.Translate where

import HipSpec.Theory

import qualified HipSpec.Lang.Rich as R
import HipSpec.Lang.Rich (Datatype(..),Constructor(..))

import HipSpec.Lang.CoreToRich
import HipSpec.Lang.SimplifyRich
import HipSpec.Lang.RichToSimple hiding (Var)
import qualified HipSpec.Lang.RichToSimple as S

import HipSpec.Lang.Simple as S
import qualified HipSpec.Lang.FunctionalFO as FO

import HipSpec.Lang.SimpleToFO as FO
import HipSpec.Lang.Deappify

import qualified HipSpec.Lang.ToPolyFOL as P
import qualified HipSpec.Lang.PolyFOL as P

import Name
import CoreSyn (CoreExpr)

import qualified Data.Map as M
import qualified Data.Set as S

import Var

import TyCon (TyCon,isNewTyCon)

import Induction.Structural

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
type Con    = (Typed Name',[Type Name'])
type TyEnv' = TyEnv Con (Type Name')

-- | Translates the type constructors
trTyCons :: [TyCon] -> (ArityMap,[Subtheory],TyEnv')
trTyCons tcs = case sequence [ fmap ((,) tc) (trTyCon tc) | tc <- tcs ]of
    Right data_types -> (con_arities,subthys,ty_env)
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
              , not (isNewTyCon tc)
              ]
            | (tc,dt@Datatype{..}) <- data_types
            , let (cls,dc_ptr_clss) = P.trDatatype (fmap Old dt)
            ]

        con_arities = M.fromList
            [ (Old (R.con_name dc),length (R.con_args dc))
            | (tc,dt) <- data_types
            , not (isNewTyCon tc)
            , dc <- data_cons dt
            ]

        m_tcs = M.fromList
            [ (Old data_ty_con,fmap Old dt)
            | (tc,dt@Datatype{..}) <- data_types
            , not (isNewTyCon tc)
            ]

        ty_env :: TyEnv'
        ty_env t0 = do
            TyCon tc tc_args <- return t0
            Datatype{..} <- M.lookup tc m_tcs
            return
                [ ( ( con_name :::
                        makeForalls data_tvs
                            (makeArrows con_args (TyCon data_ty_con (map TyVar data_tvs)))
                    , con_args'
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

-- | Translates Var/Expr-pairs to simple functions
toSimp :: [(Var,CoreExpr)] -> ([S.Function TypedName],[R.Function TypedName])
toSimp = first concat . unzip . toSimp'

toSimp' :: [(Var,CoreExpr)] -> [([S.Function TypedName],R.Function TypedName)]
toSimp' = map (uncurry to_simp)
  where
    to_simp v e = case trDefn v e of
        Right fn -> uncurry (:) . runRTS . rtsFun . fmap (fmap Old) $ simpFun fn
        Left err -> error $ "toSimp: " ++ show err

-- | Translates a bunch of simple functions into subtheories
trSimpFuns :: ArityMap -> [S.Function TypedName'] -> (ArityMap,[Subtheory])
trSimpFuns am simp_fns = (new_arities,subthys)
  where
    fo_fns :: [FO.Function Name']
    fo_fns = map stfFun simp_fns

    new_arities :: ArityMap
    new_arities = M.fromList
        [ (fn_name,length fn_args) | FO.Function{..} <- fo_fns ]

    fo_fns_zapped :: [FO.Function Name']
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

trSimpExpr :: ArityMap -> [Name'] -> S.Expr TypedName' -> P.Term LogicId
trSimpExpr am sc e = P.trExpr' sc e'
  where
    e' = zapExpr (runSTFWithScope sc (stfExpr e)) (`M.lookup` am)

