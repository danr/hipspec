module Hip.Trans.Theory where

import Hip.Trans.Core
import Hip.Trans.ProofDatatypes hiding (propName)
import Hip.Trans.Pretty
import Hip.Trans.NecessaryDefinitions
import Hip.Util

import qualified Test.QuickSpec.Term as QST

import qualified Language.TPTP as T

import Control.Arrow ((&&&),first)

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph
import Data.Tree
import Data.Maybe

data Theory = Theory { thyFuns  :: [ThyFun]
                     , thyDatas :: [Decl]
                     -- ^ Invariant: all are data declarations
                     , thyGraph :: CallGraph
                     }

theoryTopSort :: Theory -> Name -> Int
theoryTopSort (Theory _ _ (CallGraph (g,getName,getVertex))) =
    \ name -> fromMaybe (error $ "top: cannot find " ++ name)
                        (M.lookup name level_map)

  where rg     = transposeG g
        [tree] = dfs rg [fromMaybe (error $ "top: cannot find root") (getVertex Root)]
        level_map = M.fromList $ map (first (content . nodeContent . getName)) $ concat $ concat
                      [ [ zip l (repeat n) | (l,n) <- levels t `zip` [0..] ]
                      | t <- subForest tree
                      ]


theoryGraph :: Theory -> Graph
theoryGraph (Theory _ _ (CallGraph (g,_,_))) = g

theorySCC :: Theory -> Forest Name
theorySCC (Theory _ _ (CallGraph (g,getName,_)))
  = map (fmap (content . nodeContent . getName)) (scc g)

--  theoryTopSort :: Theory -> [Name]
--  theoryTopSort (Theory _ _ (CallGraph (g,getName,_)))
--    = fmap (content . nodeContent . getName) (topSort g)


data ThyFun = ThyFun { funcName       :: Name
                     -- ^ The name of this function
                     , funcTPTP       :: [T.Decl]
                     -- ^ The generated TPTP theory for this function
                     , funcPtrs       :: [(Name,Int)]
                     -- ^ Function pointer this functions uses
                     , funcFunDeps    :: Set Name
                     -- ^ Func definitions this function uses, directly or indirectly
                     , funcDataDeps   :: Set Name
                     -- ^ Data types this function uses, directly or indirectly
                     , funcDefinition :: Decl
                     -- ^ The function definition
                     , funcRecursive  :: Bool
                     -- ^ Is this function recursive?
                     , funcType       :: Maybe Type
                     -- ^ What is the type of this function?
                     }
  deriving (Eq,Ord,Show)

data Prop = Prop { proplhs  :: Expr
                 , proprhs  :: Expr
                 , propVars :: [Name]
                 , propName :: Name
                 , propType :: Type
                 , propRepr :: String
                 , propQSTerms :: (QST.Term QST.Symbol,QST.Term QST.Symbol)
                 }
  deriving (Eq,Ord,Show)

inconsistentProp :: Prop
inconsistentProp = Prop { proplhs  = Con "True" []
                        , proprhs  = Con "False" []
                        , propVars = []
                        , propName = color Red "inconsistencyCheck"
                        , propType = TyCon "Prop" [TyCon "Bool" []]
                        , propRepr = "inconsistecy check: this should never be provable"
                        }

theoryFunDecls :: Theory -> [Decl]
theoryFunDecls = map funcDefinition . thyFuns

theoryRecFuns :: Theory -> Set Name
theoryRecFuns = S.fromList . map funcName . filter funcRecursive . thyFuns

theoryFunTPTP :: Theory -> [T.Decl]
theoryFunTPTP = concatMap funcTPTP . thyFuns

theoryUsedPtrs :: Theory -> [(Name,Int)]
theoryUsedPtrs = nubSorted . concatMap funcPtrs . thyFuns

theoryFiniteType :: Theory -> Type -> Bool
theoryFiniteType = undefined

theoryDataTypes :: Theory -> [Type]
theoryDataTypes = map (\d -> TyCon (declName d) (map TyVar (declArgs d))) . thyDatas

theoryTyEnv :: Theory -> [(Name,[(Name,Type)])]
theoryTyEnv = map (declName &&& conTypes) . thyDatas
