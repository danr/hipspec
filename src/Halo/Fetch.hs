{-

    Looks into a group of CoreBinds, and complements it with all the
    missing definitions form other modules. The information is retrieved
    from the Id's Unfoldings.

    If you want to make an interface file for a file that contains all
    unfoldings (even for recursive and NOINLINE-pragma functions), use
    these three flags:

        ghc File.hs
                -fexpose-all-unfoldings         # Opt_ExposeAllUnfoldings
                -fno-ignore-interface-pragmas   # Opt_IgnoreInterfacePragmas
                -fno-omit-interface-pragmas     # Opt_OmitInterfacePragmas
                -fforce-recomp
                -ddump-hi

    Then you can view it with --show-iface and you should see the Unfoldings:

        $ ghc --show-iface File.hs
        ...
        . :: forall t t1 t2. (t1 -> t) -> (t2 -> t1) -> t2 -> t
          {- Arity: 3, HasNoCafRefs,
             Unfolding: (\ @ t @ t1 @ t2 f :: t1 -> t g :: t2 -> t1 x :: t2 ->
                         f (g x)) -}

-}
module Halo.Fetch where

import CoreSyn
import CoreFVs
import VarSet
import Var
import Id

import Halo.Util
import Halo.Shared

import Data.Maybe
import Data.Graph
    -- we use topologically sorted SCC to put things in the right CoreBind


import Debug.Trace

-- | Fetches the missing definitions from other modules
fetch :: [CoreBind] -> [CoreBind]
fetch init_bs = arrangeCoreBinds new_vars new_binders
  where
    (init_vars,exprs) = first mkVarSet (unzip (flattenBinds init_bs))

    new_binders :: [(Var,CoreExpr)]
    (all_vars,new_binders) = go init_vars exprs

    new_vars = all_vars `minusVarSet` init_vars

go :: VarSet -> [CoreExpr] -> (VarSet,[(Var,CoreExpr)])
go vs es
    | isEmptyVarSet new_vars = (vs,[])
    | otherwise = second (new_exprs ++)
                         (go (vs `unionVarSet` new_vars) (map snd new_exprs))
  where
    interesting i = let res = not (i `elemVarSet` vs) && isGlobalId i
                    in  trace ("interesting " ++ show i ++ ": " ++ show res) res

    new_vars = exprsSomeFreeVars interesting es
    new_exprs = mapMaybe maybe_unfold (varSetElems new_vars)

    maybe_unfold :: Var -> Maybe (Id,CoreExpr)
    maybe_unfold x = let res = fmap ((,) x) (maybeUnfoldingTemplate (idUnfolding x))
                     in  trace ("maybe_unfold " ++ show x ++ ": " ++ showOutputable res) res

arrangeCoreBinds :: VarSet -> [(Var,CoreExpr)] -> [CoreBind]
arrangeCoreBinds vs = map coalesce . stronglyConnComp . map (uncurry mkNode)
  where
    mkNode :: Var -> CoreExpr -> (CoreBind,Var,[Var])
    mkNode v e
        | v `elemVarSet` fvs = node (Rec [(v,e)])
        | otherwise          = node (NonRec v e)
      where
        fvs    = exprSomeFreeVars (`elemVarSet` vs) e
        node m = (m,v,varSetElems fvs)

    coalesce :: SCC CoreBind -> CoreBind
    coalesce (AcyclicSCC b) = b
    coalesce (CyclicSCC bs) = Rec (flattenBinds bs)

-- -- | Fetches missing TyCons
-- fetchTyCons :: [CoreBind] -> [TyCon] -> [TyCon]
-- fetchTyCons

