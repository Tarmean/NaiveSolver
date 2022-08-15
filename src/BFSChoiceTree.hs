{-# LANGUAGE ScopedTypeVariables #-}
-- | invariant-labeled approximate decision trees
-- Does a bfs, merges nodes when too many crop up
module BFSChoiceTree where
import Control.Monad (guard)
import Types ((|||), BoundedLattice, (<?>))
import Control.Applicative (empty)
import qualified Data.Map as M
import Overeasy.EGraph (EClassId(..))
import qualified Data.List as L
import Prettyprinter
import Debug.Trace
import GHC.Stack

import Data.Bifunctor (second)
type LevelIdx = Int
type Var = EClassId
type Cost = Int

type NodeId = (Var, LevelIdx)

data Level v s = Lvl { var :: Var, oldNodes :: DownFrontier s, nodes :: DownFrontier s, edges :: EdgeMap v }
  deriving (Eq, Ord, Show, Functor)
instance (Pretty Var, Pretty v, Pretty s) => Pretty (Level v s) where
  pretty (Lvl v nsOld ns es) = pretty "Lvl ( var = " <> pretty v  <+> pretty ",edges =" <>pretty (fmap (second M.toList) $ M.toList es)<+> pretty ", old = " <>pretty (M.toList nsOld) <> pretty ", new =" <> pretty (M.toList ns)  <> pretty ")"


class AppDiffs a where
  appDiffs :: HasCallStack => a -> [a] -> Maybe a



mkTree :: forall v s. (Show v, Ord v, AppDiffs s) => Int -> [(Var, Step s v)] -> s -> [Level v s]
mkTree limit gs s0 = go gs front0
   where
     front0 = M.singleton 0 (0, s0)
     go :: [(Var, Step s v)] -> DownFrontier s -> [Level v s]
     go [] _ = []
     go ((var, step):xs) frnt =  
         case children of
           [] -> [Lvl var frnt'' frnt'' edges']
           (c:cs) -> Lvl var frnt'' (upMerge c frnt'') edges' :c:cs
       where
         (frnt', edges) = broadcast frnt step
         (frnt'', merges) = shrinkLevel s0 limit frnt'
         edges' = applyMerge merges edges
         -- !_ = trace (show (merges, edges, edges')) ()
         children = go xs frnt''

upMerge :: (AppDiffs s, Ord v) => Level v s -> DownFrontier s -> DownFrontier s
upMerge children lvl = M.fromList $ do
    (idx, (cost, state)) <- M.toList lvl
    let outEdges = M.findWithDefault mempty idx (edges children)
        childNodes = [ x | childIdx <- M.elems outEdges, Just x <- [nodes children M.!? childIdx]]
    guard (not $ null childNodes)
    Just state' <- pure (appDiffs state (fmap snd childNodes))
    pure (idx, (cost, state'))

type DownFrontier s = M.Map LevelIdx (Int, s)
type EdgeMap v = M.Map LevelIdx (M.Map v LevelIdx)

type Step s v = s -> [(v, Cost, s)]

broadcast :: Ord v => DownFrontier s -> Step s v -> (DownFrontier s, EdgeMap v)
broadcast frnt step = (outMap, mappings)
  where
    out1 = zip[0..] $ do
        (inIdx, (baseCost, state)) <- M.toList frnt
        (choice, newCost, state') <- step state
        pure (inIdx, choice, baseCost + newCost, state')
    mappings = M.fromListWith (M.union) [(inIdx, M.singleton choice newIdx) | (newIdx, (inIdx, choice, _, _)) <- out1 ]
    outMap = M.fromList [(newIdx, (cost, newState)) | (newIdx, (_, _,cost, newState)) <- out1 ]

applyMerge :: M.Map LevelIdx LevelIdx -> EdgeMap v -> EdgeMap v
applyMerge mergeMap = M.map (M.map (\outIdx -> M.findWithDefault outIdx outIdx mergeMap))

shrinkLevel :: forall s. AppDiffs s => s -> Int -> DownFrontier s -> (DownFrontier s, M.Map LevelIdx LevelIdx)
shrinkLevel base limit frnt 
  | needRemoval <= 0 = (frnt, M.empty)
  -- | mergedState == top = (deletedNodes, M.empty)
  | otherwise = (frnt', mapping)
  where
    needRemoval = M.size frnt - limit

    byOrd = L.sortOn (fst . snd) (M.toList frnt)

    toMerge = take (1+needRemoval) byOrd
    mergeKeys = map fst toMerge
    mergeData = map (snd . snd) toMerge
    mergeCost = map (fst . snd) toMerge
    newKey = minimum mergeKeys

    deletedNodes = foldr M.delete frnt mergeKeys
    Just mergedState = appDiffs base mergeData
    mergedCost = maximum mergeCost

    frnt' :: DownFrontier s
    frnt' = M.insert newKey (mergedCost, mergedState) deletedNodes
    mapping = M.fromList [(x, newKey) | x <- mergeKeys]


