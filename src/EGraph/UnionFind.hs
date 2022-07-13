module EGraph.UnionFind where
import qualified Data.IntMap.Strict as M
import GHC.Generics (Generic)

data UF = UF (M.IntMap Int) Int
  deriving (Eq, Ord, Show, Generic)

empty :: UF
empty = UF mempty 0
genId :: UF -> (UF, Int)
genId (UF m i) = (UF m (i+1), i)

find :: UF -> Int -> (Int, UF)
find (UF m0 x) = go m0
  where
    go m i = case m M.!? i of
      Nothing -> (i, UF m x)
      Just o -> go (M.insert i o m) o
merge :: Int -> Int -> UF -> UF
merge r l m = UF (M.insert l' r m') x
  where
    (l', UF m' x) = find m l

