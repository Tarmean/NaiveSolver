{-# LANGUAGE InstanceSigs #-}

module Data.Tree.Leafy where
-- Code from Algebras for weighted search

import Control.Applicative
import Test.QuickCheck

data Tree a = Leaf a | Tree a :*: Tree a
  deriving Functor
instance Foldable Tree where
  foldMap ::  Monoid m =>
              (a -> m) ->
              Tree a -> m
  foldMap f (Leaf x)     = f x
  foldMap f (xs :*: ys)  =
    foldMap f xs <> foldMap f ys
dfs :: Tree a -> [a]
dfs = foldMap (\x -> [x])
uncons :: Tree a -> (a, Maybe (Tree a))
uncons (Leaf x)              = (x, Nothing)
uncons (Leaf x :*: xs)       = (x, Just xs)
uncons ((xs :*: ys) :*: zs)  = uncons (xs :*: (ys :*: zs))
instance Applicative Tree where
  pure = Leaf
  Leaf f <*> xs = fmap f xs
  (fl :*: fr) <*> xs = (fl <*> xs) :*: (fr <*> xs)

instance Monad Tree where
  Leaf x >>= f = f x
  (xs :*: ys) >>= f = (xs >>= f) :*: (ys >>= f)

instance Traversable Tree where
  traverse f (Leaf x) = fmap Leaf (f x)
  traverse f (xs :*: ys) = liftA2 (:*:) (traverse f xs) (traverse f ys)

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized go
    where
      go n
        | n <= 1 = fmap Leaf arbitrary
        | otherwise = do
          m <- choose (1, n - 1)
          liftA2 (:*:) (go m) (go (n-m))

  shrink (xs :*: ys) = xs : ys : map (uncurry (:*:)) (shrink (xs,ys))
  shrink (Leaf _) = []

