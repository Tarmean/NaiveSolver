{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module EGraph.Storage where

import qualified Data.Vector.Unboxed as VU
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as M
import qualified Data.HashMap.Strict as HM
import EGraph.UnionFind
import GHC.Generics (Generic)
import GHC.Base (build)

type Id = Int
type SymbolMap = M.IntMap
type ClassMap = M.IntMap
type ClassSet = IS.IntSet
type Row = VU.Vector Int
data AClass = AClass {
    class_id :: !Id,              -- ^ still you, even after everything
    tables :: !(SymbolMap Table), -- ^ One DB Table per class and symbol
    referenced_by :: !ClassSet    -- ^ Who gets dirty if our id changes
} deriving (Eq, Ord, Show, Generic)
type TableContent = VU.Vector Int
data Table = Table {
    row_width :: !Int,
    content :: !TableContent,    -- | Sorted Id[][row_width]
    references  :: !ClassSet     -- | Who do we reference, used to skip normalization
} deriving (Eq, Ord, Show, Generic)
tableSize :: Table -> Int
tableSize t = VU.length t.content `div` t.row_width
tableRow :: Int -> Table -> Row
tableRow idx t = VU.slice base end t.content
  where
    base = t.row_width * idx
    end = t.row_width

data EGraph = EGraph {
    hash_lookup :: !(SymbolMap (HM.HashMap Row Id)),
    classes :: !(ClassMap AClass),
    union_find :: !UF
} deriving (Eq, Ord, Show, Generic)

-- | We have a prefix of the row, pretend it is filled with 0's
-- How do we compare?
comparePrefix :: RowPrefix -> Row -> Ordering
comparePrefix prefix row = go 0
  where
    go !i
      | i >= VU.length prefix = EQ -- FIXME is this broken?
      | otherwise = case compare (prefix VU.! i) (row VU.! i) of
         LT -> LT
         GT -> GT
         EQ -> go (i+1)
data OnMatch = GoLeft | GoRight
binarySearch :: OnMatch -> (Int -> Ordering) -> Int -> Int -> Maybe Int
binarySearch def step = go Nothing
  where
    go acc low high
      | high < low = acc
      | otherwise = case step mid of
         LT -> go acc low (mid-1)
         EQ -> case def of
            GoLeft -> go (Just mid) low (mid-1)
            GoRight -> go (Just mid) (mid+1) high
         GT -> go acc (mid+1) high
      where mid = low + (high - low) `div` 2

tableRows :: Table -> [Row]
tableRows t = build $ \cons nil -> 
  let
    chunks = tableSize t
    go i
      | i >= chunks = nil
      | otherwise = tableRow i t `cons` go (i+1)
  in go 0
-- [Note] if this is a stepping stone for full indices this is fine
-- Otherwise, we might want to consider incremental longest common prefix arrays
regionBoundary :: OnMatch -> Int -> Table -> RowPrefix -> Maybe Int
regionBoundary def l t prefix = binarySearch def checkIdx l (tableSize t-1)
  where
    checkIdx idx = comparePrefix prefix (tableRow idx t)

testTable :: Table
testTable = Table {row_width=3, content = rows, references=mempty} 
  where
    rows = VU.fromList
         [ 0,0,0
         , 0,1,2
         , 0,1,3
         , 1,2,0
         , 1,2,2
         , 3,0,0
         ]

type RowPrefix = Row
lookupRange :: Table -> RowPrefix -> [Row]
lookupRange table prefix = build $ \cons nil ->
      let
        go i
          | i > r = nil
          | otherwise = tableRow i table `cons` go (i+1)
      in go l
  where
    (l,r) = case regionBoundary GoLeft 0 table prefix  of
      Nothing -> (1,0)
      Just l -> case regionBoundary GoRight (l+1) table prefix of
        Nothing -> (l,l)
        Just r -> (l,r)


data Modification = Mods { insertions :: ClassMap (SymbolMap Table), unifications :: VU.Vector (Id,Id)  }
-- for insertions:
-- - insert into hashmap
-- - on collision, queue unification
-- - extend class table
-- - mark class table as dirty
-- for unifications:
-- - decide which class to remove
-- - queue insertions into new class
-- - mark the referenced_by classes as dirty
applyModifications :: EGraph -> Modification -> EGraph
applyModifications eg mods = undefined
