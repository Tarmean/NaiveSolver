{-# LANGUAGE ScopedTypeVariables #-}
-- | invariant-labeled approximate decision trees
-- Does a bfs, merges nodes when too many crop up
module BFSChoiceTree where
import Control.Monad (guard)
import qualified Data.Map as M
import Overeasy.EGraph (EClassId(..))
import Data.Maybe (fromMaybe, fromJust)
import qualified Data.List as L
import Prettyprinter
import IntLike.Set (IntLikeSet)
import qualified IntLike.Set as ILS
import GHC.Stack
import Overeasy.Diff
import Data.Ord (Down(..))
import Debug.Trace

import Data.Bifunctor (second)
type LevelIdx = Int
type Var = EClassId
type Cost = Int

type NodeId = (Var, LevelIdx)

data Level v s = Lvl { var :: Var, oldNodes :: DownFrontier s, nodes :: DownFrontier s, edges :: EdgeMap v }
  deriving (Eq, Ord, Show, Functor)
instance (Pretty Var, Pretty v, Pretty s) => Pretty (Level v s) where
  pretty (Lvl v nsOld ns es) = pretty "Lvl ( var = " <> pretty v  <+> pretty ",edges =" <>pretty (fmap (second M.toList) $ M.toList es)<+> pretty ", old = " <>pretty (M.toList nsOld) <> pretty ", new =" <> pretty (M.toList ns)  <> pretty ")"



type AppDiffs d i = (Show d, DiffApply d i, Diff d i)
appDiffs :: (Lattice i, AppDiffs d i, HasCallStack) => d -> [d] -> Maybe d
appDiffs base ls = withDiffs base (fmap (diff base) ls)
withDiffs :: (Lattice i, AppDiffs d i, HasCallStack) => d -> [i] -> Maybe d
withDiffs base diffs = applyDiff (mergeDiffs diffs) base
mergeDiffs :: Lattice i => [i] -> i
mergeDiffs diffs = (foldr1 merge2 diffs)
  where
    merge2 a b = fromMaybe ltop (lintersect a b)


mkTree :: forall v s i. (Show v, Ord v, AppDiffs s i) => Int -> [(Var, Step s v)] -> s -> [Level v s]
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
         (frnt'', merges) = compactInBlocks s0 limit frnt'
         edges' = applyMerge merges edges
         -- !_ = trace (show (merges, edges, edges')) ()
         children = go xs frnt''

upMerge :: (AppDiffs s i, Ord v) => Level v s -> DownFrontier s -> DownFrontier s
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

shrinkLevel :: forall s i. AppDiffs s i => s -> Int -> DownFrontier s -> (DownFrontier s, M.Map LevelIdx LevelIdx)
shrinkLevel base limit frnt
  | trace ("shrink level" <> show (M.size frnt, limit)) False = undefined
shrinkLevel base limit frnt 
  | needRemoval <= 0 = (frnt, M.empty)
  | otherwise = trace ("shrink level" <> show frnt') (frnt', mapping)
  where
    needRemoval = M.size frnt - limit

    byOrd = L.sortOn (fst . snd) (M.toList frnt)

    toMerge = take (1+needRemoval) byOrd
    mergeKeys = map fst toMerge
    mergeData = map (snd . snd) toMerge
    mergeCost = map (fst . snd) toMerge
    newKey = myMin mergeKeys

    deletedNodes = foldr M.delete frnt mergeKeys
    mergedState = fromJust (appDiffs base mergeData)
    mergedCost = maximum mergeCost

    frnt' :: DownFrontier s
    frnt' = M.insert newKey (mergedCost, mergedState) deletedNodes
    mapping = M.fromList [(x, newKey) | x <- mergeKeys]

myMin :: (HasCallStack, Ord a) => [a] -> a
myMin [] = error "oh no"
myMin xs = minimum xs

type CompactBlock d = (IntLikeSet LevelIdx, Cost, d)
mapBlocks :: (a -> b) -> [CompactBlock a] -> [CompactBlock b]
mapBlocks f = map (\(k,c,x) -> (k,c,f x))
compactInBlocks :: AppDiffs d i => d -> Int -> DownFrontier d -> (DownFrontier d, M.Map LevelIdx LevelIdx)
compactInBlocks base limit dwn 
  | M.size dwn - limit <= 0 = (dwn, mempty)
  | otherwise = toCompact (best<>outBlocks)
  where
    (best,mergeable) = L.splitAt 6 $  L.sortOn downCost (flattenFrontier dwn)
    diffs = mapBlocks (diff base) mergeable
    newDiffs = pairMerges limit diffs
    outBlocks = mapBlocks (\d -> fromJust $ applyDiff d base) newDiffs
    downCost (_,c,_) = Down c

mapFrontier :: (a -> b) -> DownFrontier a -> DownFrontier b
mapFrontier f = M.map (\(c,x) -> (c, f x))
flattenFrontier :: DownFrontier d -> [CompactBlock d]
flattenFrontier frnt = do
    (idx, (cost, state)) <- M.toList frnt
    pure (ILS.singleton idx, cost, state)
toCompact :: Show d => [CompactBlock d] -> (DownFrontier d, M.Map LevelIdx LevelIdx)
toCompact cb = (frnt, mapping)
  where
    -- !_ = trace ("toCompact" <> show (frnt, mapping)) (error "")
    frnt = M.fromList [(minSet x, (cost, state)) | (x, cost, state) <- cb]
    mapping = M.fromListWith undefined [(k, minSet x) | (x, _, _) <- cb, k <- ILS.toList x]
    minSet = fst . fromJust . ILS.minView
mergeBlock :: Lattice d => CompactBlock d -> CompactBlock d -> CompactBlock d
mergeBlock (l,c1,r) (a,c2,b) = (ILS.union l a, max c1 c2, fromMaybe ltop (lintersect r b))

pairMerges :: Lattice d => Int -> [CompactBlock d] -> [CompactBlock d]
pairMerges goal blocks0 = go (length blocks0) blocks0
  where
    go cur blocks
      | cur <= goal = blocks
      | otherwise = go (cur `div` 2) (mergePairs blocks)

mergePairs :: Lattice d => [CompactBlock d] -> [CompactBlock d]
mergePairs [] = []
mergePairs [x] = [x]
mergePairs (x:y:xs) = mergeBlock x y : mergePairs xs
