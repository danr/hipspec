{-# LANGUAGE DeriveFunctor #-}
module Hip.Trans.NecessaryDefinitions where

import Hip.Trans.ParserInternals
import Hip.Trans.Core
import Hip.Trans.Constructors

import Data.List
import Data.Maybe
import Control.Arrow ((***),second)

import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M
import Data.Map (Map)

import Data.Generics.Uniplate.Operations

import Data.Graph
import Data.Array

data Content a = Root                -- Root node. All constructors point to it.
               | F { content :: a }  -- Functions
               | C { content :: a }  -- Constructors
  deriving (Eq,Ord,Show,Functor)

safeContent :: Content Name -> Name
safeContent Root = "Root"
safeContent c    = content c



isF :: Content a -> Bool
isF F{} = True
isF _   = False

type Node = (Name,Content Name,[Content Name])

newtype CallGraph =
  CallGraph { getCallGraph :: (Graph, Vertex -> Node, Content Name -> Maybe Vertex) }

nodeContent :: Node -> Content Name
nodeContent (_,c,_) = c

getEdges :: Node -> [Content Name]
getEdges (_,_,es) = es

declsToGraph :: [Decl] -> CallGraph
declsToGraph ds = CallGraph (graphFromEdges (("",Root,[]) : fun_nodes ++ con_nodes))
  where
    (fun_decls,data_decls,_) = partitionDecls ds

    setsToContent :: (Set Name,Set Name) -> [Content Name]
    setsToContent (fs,cs) = map F (S.toList fs) ++ map C (S.toList cs)

    fun_nodes :: [Node]
    fun_nodes = [ (declName d,F (declName d),setsToContent (usedFC d)) | d <- fun_decls ]

    con_nodes :: [Node]
    con_nodes = [ (con_name,C (con_name),Root:setsToContent (usedSets))
                | d <- data_decls
                , let usedSets@(_,cons) = usedFC d
                , con_name <- S.toList cons
                ]

{-
getNode :: CallGraph -> Name -> Node
getNode (CallGraph (_,vertexToNode,nameToVertex)) name
  = vertexToNode
  . fromMaybe (error $ "getNode: " ++ n)
  . nameToVertex
-}

-- | Is this function recursive, by itself, or mutually?
recursive :: CallGraph -> Name -> Bool
recursive (CallGraph (g,_,getVertex)) n = any (\via -> path g via v) (g ! v)
  where
    v :: Vertex
    v = fromMaybe (error $ "recursive: " ++ n) (getVertex (F n))

-- | Which functions do this set of functions call, transitively?
iterateFCs :: CallGraph -> Set Name -> (Set Name,Set Name)
iterateFCs (CallGraph (g,getNode,getVertex)) fun_set = res
  where
    vertices :: [Vertex]
    vertices = map (\n -> fromMaybe (error $ "iterateFCs: " ++ n)
                        . getVertex . F $ n) (S.toList fun_set)

    reachables :: [Content Name]
    reachables = map (nodeContent . getNode)
               $ concatMap (reachable g) vertices

    res :: (Set Name,Set Name)
    res = (S.fromList . map content *** S.fromList . map content)
          (partition isF reachables)


-- Funs and Cons
class FC a where
   usedFC :: a -> (Set Name,Set Name)

usedFs :: FC a => a -> Set Name
usedFs = fst . usedFC

-- | Which functions call these functions, transitively?
--   TODO: Rewrite with the graph
callers :: [Decl] -> Set Name -> Set Name
callers funDecls = go
  where
    -- For each function, which functions does it call in one step?
    usedFss :: [(Name,Set Name)]
    usedFss = [ (declName d,usedFs d) | d <- funDecls ]

    -- For each function, which function calls it in one step?
    callsMap :: Map Name (Set Name)
    callsMap = M.fromList
               [ (n,S.fromList (map fst (filter (S.member n . snd) usedFss)))
               | d <- funDecls
               , let n = declName d
               ]

    safeLookup :: Name -> Set Name
    safeLookup f = fromMaybe S.empty (M.lookup f callsMap)

    go fs | S.null newfs = fs
          | otherwise    = go (fs `S.union` fs')
      -- Get the new functions from here
      where fs' :: Set Name
            fs' = S.unions (map safeLookup (S.toList fs))
            newfs = fs' S.\\ fs

instance FC Pattern where
  usedFC p = (S.fromList [ x | PVar x <- universeBi p ]
             ,S.fromList [ x | PCon x _ <- universeBi p ]
             )

(><) :: (a -> b -> c) -> (a' -> b' -> c') -> (a,a') -> (b,b') -> (c,c')
(f >< g) (x1,y1) (x2,y2) = (x1 `f` x2,y1 `g` y2)

instance FC Branch where
  usedFC (NoGuard p :-> e) = (S.difference >< S.union) (usedFC e) (usedFC p)
  usedFC (Guard p g :-> e) = second (S.insert trueName) $
                                 (S.difference >< S.union)
                                 ((S.union >< S.union) (usedFC e) (usedFC g))
                                 (usedFC p)

instance FC Expr where
  usedFC e = (S.fromList (mapMaybe vars (universe e))
             ,S.fromList [ c | Con c _ <- universe e])
    where
      vars (App f xs) = Just f
      vars (Var x)    = Just x
      vars _          = Nothing


instance FC Body where
  usedFC (Expr e) = usedFC e
  usedFC (Case e brs) = (S.union >< S.union)
                        (usedFC e)
                        ((S.unions *** S.unions) (unzip (map usedFC brs)))

instance FC Decl where
   usedFC (Func name args body) =
      let (fs,cs) = usedFC body
      in  ((fs S.\\ S.fromList args),cs)
   usedFC d@Data{} = (S.empty,S.fromList . map fst . conNameArity $ d)
   usedFC _ = (S.empty,S.empty)


