module Data.Utils where
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Prettyprinter as P
import qualified Prettyprinter.Render.String as P
import Control.Monad.State (evalState, get, put)
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

docToString :: P.Doc s -> String
docToString = P.renderString . P.layoutPretty P.defaultLayoutOptions

pprint :: P.Pretty a => a -> IO ()
pprint = putStrLn . docToString . P.pretty
pshow :: P.Pretty a => a -> String
pshow = docToString . P.pretty

zipFoldableWith :: (Traversable f) => (a -> b -> c) -> f a -> f b -> f c
zipFoldableWith f xs ys 
  | length ls /= length rs = error "zipFoldableWith: length doesn't match"
  | otherwise = evalState (traverse putBack xs) os
   where
     ls = F.toList xs
     rs = F.toList ys
     os = zipWith f ls rs

     putBack _ = do
        s <- get
        case s of
          x:vs -> put vs >> return x
          [] -> error "zipFoldableWith: empty state"
