module Monad.Levels where

-- code from algebras for weighted search
import Data.Bag
import Control.Applicative
import Control.Monad
import Prelude hiding ((++))
import Data.Maybe (listToMaybe)

import qualified Monad.ConcreteBreadthFirst as Concrete
import Control.Monad.Trans (MonadTrans(..))

newtype HypM' m a b = HypM { invokeM :: (m (HypM' m a b) -> a) -> b }

newtype LevelsT m a = LevelsT { runLevelsT :: forall r. (Bag a -> m r -> m r) -> m r -> m r }


instance Functor (LevelsT m) where
  fmap f xs = LevelsT (\c -> runLevelsT xs (c . fmap f))

instance Monad m => Applicative (LevelsT m) where
  pure x = LevelsT (\c n -> c (Sing x) n)
  (<*>) = ap

instance Monad m => Alternative (LevelsT m) where
  empty = LevelsT (\_ n -> n)
  xs <|> ys = LevelsT (\c n ->
        let
          xf x xk = pure (HypM (\yk -> yk xk x))

          xb = pure (HypM (\yk -> yk xb Empty))

          yf y yk = pure (\xk x ->
                    c  (x <> y)
                       (liftA2M invokeM xk yk))

          yb xk Empty  = n
          yb xk x      = c x (xk >>= flip invokeM yb)

        in liftA2M invokeM
             (runLevelsT xs xf xb)
             (runLevelsT ys yf (pure yb)))
liftA2M ::  Monad m =>
            (a -> b -> m c) ->
            m a -> m b -> m c
liftA2M f xs ys = do
  x <- xs
  y <- ys
  f x y

delay :: Monad m => LevelsT m a -> LevelsT m a
delay x = wrapLevelsT (pure x)

instance MonadTrans LevelsT where
    lift m = LevelsT (\c n -> m >>= \x -> c (Sing x) n)
liftLevelsT :: Monad m => m (LevelsT m a) -> LevelsT m a
liftLevelsT xs = LevelsT (\c n -> xs >>= \xs' -> runLevelsT xs' c n)

wrapLevelsT :: Monad m => m (LevelsT m a) -> LevelsT m a
wrapLevelsT xs = LevelsT (\c n -> c Empty (xs >>= \xs' -> runLevelsT xs' c n))

instance Monad m => Monad (LevelsT m) where
  xs >>= k = liftLevelsT (runLevelsT xs f (pure empty))
    where
      f x xs = pure (foldr ((<|>) . k) (wrapLevelsT xs) x)

concrete :: Applicative m => LevelsT m a -> Concrete.LevelsT m a
concrete xs = Concrete.LevelsT (runLevelsT xs (\x xs -> pure (Just (x, Concrete.LevelsT xs))) (pure Nothing))

collect :: Monad m => Int -> LevelsT m a -> m [a]
collect n = Concrete.collect n . concrete


folding :: (a -> m r -> m r) -> m r -> LevelsT m a -> m r
folding f n lvl = runLevelsT lvl (\x xs -> foldr f xs x) n

toMaybe :: Monad m => LevelsT m a -> m (Maybe a)
toMaybe  = fmap listToMaybe . Concrete.collect 1 . concrete

pyth :: IO [(Int,Int,Int)]
pyth = collect 10 $ do
  let nats = LevelsT (\c n -> foldr (\x xs -> print x >> c (Sing x) xs) n [1..])
  x <- nats
  y <- nats
  z <- nats
  guard (x * x + y * y == z * z)
  pure (x,y,z)

-- >>> pyth
-- [(3,4,5),(4,3,5),(6,8,10),(8,6,10),(5,12,13),(12,5,13),(9,12,15),(12,9,15),(8,15,17),(15,8,17)]

(++) :: LevelsT m a -> LevelsT m a -> LevelsT m a
xs ++ ys = LevelsT (\c -> runLevelsT xs c . runLevelsT ys c)

(>>-) :: LevelsT m a -> (a -> LevelsT m b) -> LevelsT m b
xs >>- k = LevelsT (\c -> runLevelsT xs (\baga zr -> (foldr (\cur acc ->  runLevelsT (k cur) c acc) zr baga)))



