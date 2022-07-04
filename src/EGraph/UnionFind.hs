module EGraph.UnionFind where
import qualified Data.IntMap.Strict as M
import GHC.Generics (Generic)

data UF = UF (M.IntMap Int) Int
  deriving (Eq, Ord, Show, Generic)

genId :: UF -> (UF, Int)
genId (UF m i) = (UF m (i+1), i)

find :: UF -> Int -> (UF, Int)
find (UF m0 x) = go m0
  where
    go m i = case m M.!? i of
      Nothing -> (UF m x, i)
      Just o -> go (M.insert i o m) o
merge :: Int -> Int -> UF -> UF
merge r l m = UF (M.insert l' r m') x
  where
    (UF m' x, l') = find m l

