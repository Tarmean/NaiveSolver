{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Mutable.Lens where

import Data.Functor.Compose
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.State
import Data.Monoid
import Control.Lens




-- | A 'mutable borrow'
-- Treat an in-place lens as a normal lens by returning the old location
-- mut (#counters .$ ixM 1) .= 4
mut :: (Functor f, Functor m, Traversable f) => LValLensLike f m s a -> MLensLike' f m s a
mut l k s = s <$ l k s

instance (MonadIO m, Applicative f, Monad (Compose m f)) => MonadIO (Compose m f) where
    liftIO m = Compose $ pure <$> liftIO m

-- | Compose a getter with an in-place
-- 
(.$) ::  (Functor f, Applicative m) => MLensLike (Const (f ())) m s t a a -> LValLensLike f m a x -> LValLensLike f m s x
(.$) l r f s = Compose $ fmap getConst $ getCompose $ l (\a -> Compose $ Const <$> getCompose (r f a)) s
infixr 9 .$

-- | Mutate a place, possibly returning a new value
-- #fooArray %- \v ->
--     V.ensureCapacity (V.length v + 1) v
(=-) :: MonadState s m => MLensLike' Identity m s a -> (a -> m a) -> m ()
(=-) = mutateP

(%-) :: MonadState s m => MLensLike' Identity m s a -> (a -> a) -> m ()
(%-) l f = mutateP l (pure . f)

(.-) :: MonadState s m => MLensLike Identity m s s a a -> a -> m ()
(.-) l x = mutateP l (\_ -> pure x)

(?-) :: MonadState s m => MLensLike' Identity m s (Maybe a) -> a -> m ()
(?-) l x = l .- Just x

usingP :: MonadState s m => MGetter x m s t a b -> (a -> m x) -> m x
usingP l inj = do
  s <- get 
  mkGetter l s (inj)
-- usesP :: MonadState s m => MGetter x m s t a b -> (a -> x) -> m x
-- usesP l inj = usingP l (pure . inj)
useP :: MonadState s m => MGetter a m s t a b -> m a
useP l = usingP l pure
preuseP :: MonadState s m => MGetter (First a) m s t a b -> m (Maybe a)
preuseP l = getFirst <$> usingP l (pure . First . Just)
toListOfP :: MonadState s m => MGetter [a] m s t a b -> m [a]
toListOfP l = usingP l (pure . pure)
   
hasM :: MonadState s m => MGetter Any m s t a b -> m Bool
hasM l =do
  s <- get 
  getAny <$> mkGetter l s (const $ pure (Any True))

-- | Mutate a place
mutateP :: MonadState s m => MLensLike' Identity m s a -> (a -> m a) -> m ()
mutateP l f = do
  s <- get
  s' <- overM s
  put s'
  where overM s = fmap runIdentity $ getCompose $  l (Compose . fmap Identity .  f) s

mapP :: MonadState s m => MLensLike' Identity m s a -> (a -> a) -> m ()
mapP l f = mutateP l (pure . f)

-- | Mutate a place and also return a value
updateP :: (MonadState s m) => MLensLike' (With x) m s a -> (a -> m (a, x)) -> m x
updateP f k = do
  s <- get
  With x s' <- getCompose $ f (Compose . fmap (uncurry $ flip With) . k) s
  put s'
  pure x
-- | Swap location with a new value, return the old value
--
--     takeArray :: M (V.Vector Int)
--     takeArray = swapP #theArray (V.new 0)
swapP :: (MonadState s m) => MLensLike' (With a) m s a -> m a -> m a
swapP f k = updateP f (\a -> (, a) <$> k)


mkGetter :: Functor m => MGetter x m s t a b -> s -> (a -> m x) -> m x
mkGetter l s f = fmap getConst $ getCompose $ l (Compose . fmap Const . f) s

nonM :: (Monad m) => m a -> MLens m (Maybe a) a
nonM m k Nothing = Just <$> Compose (getCompose . k =<< m)
nonM _ k (Just a) = Just <$> k a


type MGetter r m s t a b = (a -> Compose m (Const r) b) -> s -> Compose m (Const r) t

-- Most general monadic lenses
type MLensLike' f m s a = MLensLike f m s s a a
type MLensLike f m s t a b =(a -> Compose m f b) -> s -> Compose m f t
type MLens m s a = forall f. Traversable f => (a -> Compose m f a) -> s -> Compose m f s

-- Mutating lenses don't return anything because they update in-place
type LValLens m s a = forall f. Traversable f => (a -> Compose m f a) -> s -> Compose m f ()
type LValLensLike f m s a = Traversable f => (a -> Compose m f a) -> s -> Compose m f ()

-- Mutating traversals don't return anything because they update in-place
type LValTraversal m s a = forall f. (Monoid (f ()), Applicative f, Traversable f) => (a -> Compose m f a) -> s -> Compose m f ()
type LValTraversalLike f m s a = (Applicative f, Traversable f) => (a -> Compose m f a) -> s -> Compose m f ()

data With s a = With s a
  deriving (Functor, Traversable, Foldable)
instance Monoid s => Applicative (With s) where
  pure = With mempty
  With l f <*> With r a = With (l <> r) (f a)

