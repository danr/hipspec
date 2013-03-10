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


    An important thing is to use realIdUnfolding instead of
    idUnfolding, otherwise recursive unfoldings will be lost.

-}
module Halo.Fetch where

import CoreFVs
import CoreSyn
import Id
import TyCon
import VarSet

import Halo.FreeTyCons
import Halo.Shared
import Halo.Util

import Data.Maybe
import Data.List
import Data.Graph
    -- we use topologically sorted SCC to put things in the right CoreBind

import Control.Monad.Writer
    -- to debug unfoldings

-- | Fetches the missing definitions from other modules
fetch :: (Var -> Bool) -> [CoreBind] -> ([CoreBind],String)
fetch ok init_bs = (arrangeCoreBinds new_vars new_binders,unlines debug)
  where
    (init_vars,exprs) = first mkVarSet (unzip (flattenBinds init_bs))

    new_binders :: [(Var,CoreExpr)]
    ((all_vars,new_binders),debug) = runWriter (go ok init_vars exprs)

    new_vars = all_vars `minusVarSet` init_vars

write :: a -> Writer [a] ()
write = tell . return

go :: (Var -> Bool) -> VarSet -> [CoreExpr] -> Writer [String] (VarSet,[(Var,CoreExpr)])
go ok vs es
    | isEmptyVarSet new_vars = write "No more unvisited expressions" >> return (vs,[])
    | otherwise = do
        write $ "Interesting variables this round: " ++ showOutputable new_vars
        new_exprs <- catMaybes <$> mapM maybe_unfold (filter ok $ varSetElems new_vars)
        second (new_exprs ++) <$> go ok (vs `unionVarSet` new_vars) (map snd new_exprs)
  where
    new_vars = exprsSomeFreeVars interesting es

    interesting i = not (i `elemVarSet` vs) && isGlobalId i

    maybe_unfold :: Var -> Writer [String] (Maybe (Id,CoreExpr))
    maybe_unfold x = do
        let res = fmap ((,) x) (maybeUnfoldingTemplate (realIdUnfolding x))
        write $ "Unfolding of " ++ showOutputable x ++ ": " ++ showOutputable res
        return res

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

-- | Fetches used TyCons
fetchTyCons :: [CoreBind] -> [TyCon]
fetchTyCons = sort . unions . map freeTyCons . snd . unzip . flattenBinds
  where
    unions = foldl union []
