{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
-- {-# LANGUAGE DuplicateRecordFields #-}
module IncrementalDatalog where


import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as MM
import Control.Applicative
import qualified Data.IntMap as IM
import qualified Data.Set as S


data TheDefault a = Old a | New a | None
  deriving (Show, Eq, Ord, Functor)
data Table k v = Table { old :: M.Map k v, new :: M.Map k v, def :: Maybe v }
  deriving (Show, Eq, Ord, Functor)

instance Ord k => Alternative (Table k) where
  empty = Table M.empty M.empty Nothing
  Table o n d <|> Table o' n' d' = Table (M.union o o') (M.union n n') (d <|> d')

instance Ord k => Applicative (Table k) where
    pure x = Table mempty mempty (Just x)
    Table f g h <*> Table x y z = Table (M.map unwrap $ merge2 newL newR f x) newMerged  (h <*> z)
      where
        newMerged = M.map unwrap $ merge2 newL newR g y +++ merge2 old newR f y +++ merge2 newL old g x
        merge2 :: (MM.SimpleWhenMissing k (a -> b) (Either b b)
                  -> MM.SimpleWhenMissing k a (Either b b)
                  -> M.Map k (a -> b)
                  -> M.Map k a
                  -> M.Map k (Either b b))
        merge2 onL onR = MM.merge onL onR (MM.zipWithMatched (\_ c v -> Right (c v)))

        (+++) :: M.Map k (Either b b) -> M.Map k (Either b b) -> M.Map k (Either b b)
        (+++) = MM.merge (MM.preserveMissing) (MM.preserveMissing) (MM.zipWithMatched merge1)
        unwrap (Left a) = a
        unwrap (Right a) = a
        merge1 _ (Right a) _ = Right a
        merge1 _ (Left _) (Right a) = Right a
        merge1 _ a _ = a
        newL = MM.mapMaybeMissing (\_ c -> Left . c <$> z)
        newR = MM.mapMaybeMissing (\_ v -> (\c -> Left (c v)) <$> h)
        old = MM.dropMissing

type Id = Int
data DB k v = DB { table :: IM.IntMap v, index :: M.Map k (S.Set Id) }
  deriving (Eq, Ord, Show, Functor)
-- Idea: seperate indices from tables
-- Table: IntMap Id a
-- Index: Map k (S.IdSet)
--
-- - We pull indices to the front using some combinator
-- - Applicative merges on indices, giving a stream `[(Id,Id)]`
-- - Join tables on those indices
-- - Later, re-add default fallback for outer joins 


userTable :: Table Int String
userTable = Table (M.fromList [(2, "Bob"), (3, "Charlie")]) (M.fromList [(1, "Alice")])  Nothing


heightTable :: Table Int Int
heightTable = Table (M.fromList [(1, 25), (2, 7)]) (M.fromList [(4, 14)])  Nothing


test :: Table Int (String, Int)
test = do
   l <- userTable
   r <- heightTable
   pure (l,r)


