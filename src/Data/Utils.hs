module Data.Utils where
import qualified Data.Foldable as F
import qualified Data.List as L
compact :: (Ord a, Show a, Foldable t, Num a) => t a -> String
compact t = L.intercalate "," $ go0 $ L.sort $ F.toList t
  where
    go0 (x:xs) = go x x xs
    go0 [] = []
    single l r
      | l == r = show l
      | otherwise = show l <> "-" <> show r
    go l r (x:xs)
      | x == r+1 = go l x xs
      | otherwise = single l r : go x x xs
    go l r [] = [single l r]
