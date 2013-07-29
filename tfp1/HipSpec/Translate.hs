{-# LANGUAGE RecordWildCards #-}
module HipSpec.Translate where

import HipSpec.Theory

import qualified Lang.Rich as R
import Lang.Rich (Datatype(..),Constructor(..))

import Lang.CoreToRich
import Lang.SimplifyRich
import Lang.RichToSimple hiding (Var)
import qualified Lang.RichToSimple as S

import Lang.Simple as S
import qualified Lang.FunctionalFO as FO

import Lang.SimpleToFO as FO
import Lang.Deappify

import qualified Lang.ToPolyFOL as P
import qualified Lang.PolyFOL as P

import Name
import CoreSyn (CoreExpr)

import qualified Data.Map as M
import qualified Data.Set as S

import Var

import TyCon (TyCon)

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
trTyCons tcs = case mapM trTyCon tcs of
    Right data_types -> (con_arities,subthys,ty_env)
      where
        subthys = concat
            [ calcDeps subtheory
                { defines = Type data_ty_con
                , clauses = cls
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
              ]
            | dt@Datatype{..} <- data_types
            , let (cls,dc_ptr_clss) = P.trDatatype (fmap Old dt)
            ]

        con_arities = M.fromList
            [ (Old (R.con_name dc),length (R.con_args dc))
            | dt <- data_types
            , dc <- data_cons dt
            ]

        m_tcs = M.fromList
            [ (data_ty_con,dt)
            | dt@Datatype{..} <- map (fmap Old) data_types
            ]

        ty_env :: TyEnv'
        ty_env t0 = do
            TyCon tc tc_args <- return t0
            let same_ty_con t = case t of
                    TyCon tc' _ -> tc' == tc
                    _           -> False
            Datatype{..} <- M.lookup tc m_tcs
            return
                [ ( ( con_name :::
                        makeForalls data_tvs
                            (makeArrows con_args (TyCon data_ty_con (map TyVar data_tvs)))
                    , con_args'
                    )
                  , [ case collectArrTy t of
                        (ts,r) | same_ty_con r -> case ts of
                            [] -> Rec r
                            _  -> Exp r ts
                        _                      -> NonRec t
                    | t <- con_args'
                    ]
                  )
                | Constructor{..} <- data_cons
                , let con_args' = map (substManyTys (zip data_tvs tc_args)) con_args
                ]

    Left err -> error $ "trTyCons: " ++ show err


-- | Translates Var/Expr-pairs to simple functions
toSimp :: [(Var,CoreExpr)] -> [S.Function (S.Var Name)]
toSimp = concatMap (uncurry to_simp)
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

