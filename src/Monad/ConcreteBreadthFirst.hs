module Monad.ConcreteBreadthFirst where
-- code from algebras for weighted search

import Data.Bag
import Data.Bifunctor
import Control.Applicative
import Control.Monad
import Prelude hiding (concat)

newtype LevelsT m a = LevelsT { runLevelsT :: m (Maybe (Bag a, LevelsT m a)) }

foldrM :: Monad m => (Bag a -> m b -> m b) -> m b -> LevelsT m a -> m b
foldrM f b xs = runLevelsT xs >>= maybe b (uncurry f . fmap (foldrM f b))

wrap :: Applicative m => LevelsT m a -> LevelsT m a
wrap xs = LevelsT (pure (Just (Empty, xs)))

instance Functor m => Functor (LevelsT m) where
  fmap f = LevelsT . fmap (fmap (bimap (fmap f) (fmap f))) . runLevelsT

instance Monad m => Applicative (LevelsT m) where
  pure = LevelsT . pure . Just . (,empty) . Sing
  (<*>) = ap

instance Monad m => Monad (LevelsT m) where
  xs >>= k =
      LevelsT (runLevelsT xs >>= maybe b f)
    where
      b = pure Nothing
      f (x,xs) = runLevelsT
        (foldr ((<|>) . k) (wrap (xs >>= k)) x)
      wrap xs = LevelsT (pure (Just (Empty, xs)))
instance Monad m => Alternative (LevelsT m) where
  empty = LevelsT (pure Nothing)
  LevelsT xs <|> LevelsT ys =
      LevelsT (liftA2 go xs ys)
    where
      go Nothing ys  = ys
      go xs Nothing  = xs
      go (Just (x, xs)) (Just (y, ys)) =
        Just (x <> y, xs <|> ys)

instance Monad m => MonadPlus (LevelsT m)

collect :: Monad m => Int -> LevelsT m a -> m [a]
collect n xs = fmap (take n) (go n xs)
  where
    go n xs
      | n <= 0 = pure []
      | otherwise = runLevelsT xs >>= maybe (pure []) (\(x,xs) -> fmap (flip (foldr (:)) x) (go (n - length x) xs))

unfoldrM :: Functor m => (b -> m (Maybe (Bag a, b))) -> b -> LevelsT m a
unfoldrM f b = LevelsT (fmap (fmap (fmap (unfoldrM f))) (f b))


pyth :: IO [(Int,Int,Int)]
pyth = collect 1 $ do
  let nats = unfoldrM (\n -> Just (Sing n, n+1) <$ print n) 1
  x <- nats
  y <- nats
  z <- nats
  guard (x * x + y * y == z * z)
  pure (x,y,z)
concat :: Monad m => LevelsT m a -> LevelsT m a -> LevelsT m a
concat xs ys = LevelsT (runLevelsT xs >>= maybe (runLevelsT ys) (pure . Just . fmap (`concat` ys)))
(>>-) :: Monad m => LevelsT m a -> (a -> LevelsT m b) -> LevelsT m b
xs >>- k = LevelsT (foldrM f (runLevelsT empty) xs)
  where
    f x xs = runLevelsT (concat (foldr ((<|>) . k) empty x) (LevelsT xs))
