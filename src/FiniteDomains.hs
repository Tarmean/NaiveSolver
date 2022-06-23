{-# LANGUAGE TemplateHaskell #-}
module FiniteDomains where

import qualified Data.Set as S
import Types
import Test.QuickCheck
    ( quickCheckAll, Testable(property), Property )

data FiniteDomain a = FD { unFiniteDomain :: S.Set a }
  deriving (Eq, Ord, Show)

newtype SudokuNum = SD Int
  deriving (Eq, Ord, Show, Enum)
instance Bounded SudokuNum where
  minBound = SD 1
  maxBound = SD 9
class Universe a where
    universe :: a
instance (Ord a, Bounded a, Enum a) => Universe (FiniteDomain a) where
    universe = FD $ S.fromList [minBound..maxBound]
instance (Ord a) => PContains (FiniteDomain a) where
  compareC (FD l) (FD r)
      | l == r = Just EQ
      | l `S.isSubsetOf` r = Just LT
      | r `S.isSubsetOf` l = Just GT
      | otherwise = Nothing

instance (Ord a) => PSemigroup (FiniteDomain a) where
  
  (<?>) (FD a) (FD b)
    | S.null intersect = Nothing
    | otherwise = Just $ FD intersect
    where intersect = S.intersection a b
instance (Ord a) => PLattice (FiniteDomain a) where
  (<||>) (FD a) (FD b) = Just $ FD $ S.union a b

instance (Bounded a, Enum a, Ord a) => RegularSemigroup (FiniteDomain a) where
  FD a ==> FD b = FD (b `S.union` S.difference (unFiniteDomain universe)  a)
instance (Bounded a, Enum a, Ord a) => PMonoid (FiniteDomain a) where
  pempty = universe
instance (Bounded a, Enum a, Ord a) => BoundedLattice (FiniteDomain a) where
  bot = FD S.empty
  isBot (FD a) = S.null a

ft :: [Int] -> FiniteDomain SudokuNum
ft = FD . S.fromList . map (SD . succ . (`mod` 9))

prop_impl_conj_r, prop_impl_conj_l, prop_impl_refl , prop_impl_full  , prop_impl_empty :: Property
prop_impl_conj_l = property $ \l r -> ((ft l ==> ft r) &&& ft l) == ft l &&& ft r
prop_impl_conj_r = property $ \l r -> ((ft l ==> ft r) &&& ft r) == ft r
prop_impl_refl = property $ \a -> top == (ft a ==> ft a)
prop_impl_full = property $ \a -> top == (ft a ==> top)
prop_impl_empty = property $ \l -> bot ==> ft l== top
prop_conj_assoc, prop_conj_idempotent, prop_conj_commutative, prop_conj_absorbing, prop_conj_neutral, prop_conj_shrinking :: Property
prop_conj_assoc = property $ \a b c -> (ft a &&& ft b) &&& ft c == ft a &&& (ft b &&& ft c)
prop_conj_idempotent = property $ \a -> (ft a &&& ft a) == ft a
prop_conj_commutative = property $ \a b -> (ft a &&& ft b) == (ft b &&& ft a)
prop_conj_absorbing = property $ \a -> ft a &&& top == ft a
prop_conj_neutral = property $ \a -> ft a &&& bot == bot
prop_conj_shrinking = property $ \a b -> ft a &&& ft b `contains` ft a

prop_disj_assoc, prop_disj_idempotent, prop_disj_commutative, prop_disj_absorbing, prop_disj_neutral, prop_disj_growing :: Property
prop_disj_assoc = property $ \a b c -> (ft a ||| ft b) ||| ft c == ft a ||| (ft b ||| ft c)
prop_disj_idempotent = property $ \a -> (ft a ||| ft a) == ft a
prop_disj_commutative = property $ \a b -> (ft a ||| ft b) == (ft b ||| ft a)
prop_disj_absorbing = property $ \a -> ft a ||| top == top
prop_disj_neutral = property $ \a -> ft a ||| bot == ft a
prop_disj_growing = property $ \a b -> ft a `contains` (ft a ||| ft b)
return []
checkAll :: IO Bool
checkAll = $quickCheckAll
