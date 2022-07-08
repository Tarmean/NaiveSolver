{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingVia #-}
module Data.Mutable.Lens where

import Data.Functor.Compose
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.State
import Data.Monoid
import Control.Lens
import Data.Mutable.Internal.MutZoom (JoinZoom (joinZoom))
import Data.Mutable.Distributive
import Control.Monad.Primitive (PrimState)
import Data.Profunctor
import Control.Arrow (Kleisli)
import Data.Distributive




-- | A 'mutable borrow'
-- Treat an in-place lens as a normal lens by returning the old location
-- mut (#counters .$ ixM 1) .= 4
mut :: (Functor f, Functor m) => LValLensLike f m s a -> MLensLike' f m s a
mut l k s = s <$ l k s

instance (Monad m, Monad f, Distributes m f) => Monad (Compose m f) where
    (Compose m) >>= f = Compose $ fmap join $ join (fmap (traverseD (getCompose . f)) m)
instance (MonadIO m, Applicative f, Monad (Compose m f)) => MonadIO (Compose m f) where
    liftIO m = Compose $ pure <$> liftIO m

-- | Compose a getter with an in-place
-- 
(.$) ::  (Functor f, Applicative m) => MLensLike (Const (f ())) m s t a a -> LValLensLike f m a x -> LValLensLike f m s x
(.$) l r f s = Compose $ fmap getConst $ getCompose $ l (\a -> Compose $ Const <$> getCompose (r f a)) s
infixr 9 .$

-- | Call a method on a location
--
--     pushCollection idx val = mut(#collections .$ atM idx . nonP (V.new 1))&.(push val)
--
-- This could re-allocate the vector we push on, invalidating the old reference.
-- To reflect this, we use `push :: MonadState (V.Vector (PrimState m) a) m => m ()`.
-- The state monad carries the implicit 'this' reference - to call a method, we must zoom into the `this` location.
-- While calling
-- - The outer state contains the containing enviroment, such as `#collections`
-- - The focused (this) state contains the vector we update
-- - The monadic lens doesn't have access to either state, but it can use the underlying monad
(&.) :: (JoinZoom m1 (Zoomed m2 c t), Zoom m2 n s t, Applicative m1) => ((s -> Compose m1 (Zoomed m2 c) s) -> t -> Compose m1 (Zoomed m2 c) t) -> m2 c -> n c
(&.) l m = zoom flattenLens m
  where flattenLens l' s = joinZoom $ getCompose $ l (Compose . pure . l') s 

class CovHack a b | a -> b, b -> a
instance CovHack a b => CovHack a b
-- | Mutate a place, possibly returning a new value
-- #fooArray %- \v ->
--     V.ensureCapacity (V.length v + 1) v
infix 4 &->
infix 4 &=
infix 4 &.
(&->) :: MonadState s m => MLensLike' Identity m s a -> (a -> m a) -> m ()
(&->) = mutateP
(&=) :: MonadState s m => MLensLike Identity m s s a a -> a -> m ()
(&=) l x = mutateP l (\_ -> pure x)

usingP :: MonadState s m => MGetter x m s t a b -> (a -> m x) -> m x
usingP l inj = do
  s <- get 
  mkGetter l s (inj)
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
tryUpdateP :: (MonadState s m) => MLensLike' (Compose Maybe (With x)) m s a -> (a -> m (a, x)) -> m (Maybe x)
tryUpdateP f k = do
  s <- get
  out <-  getCompose $ f (Compose . fmap (Compose . Just . uncurry (flip With)) . k) s
  case getCompose out of
      Nothing -> pure Nothing
      Just (With x s') -> do
          put s'
          pure (Just x)
-- | Swap location with a new value, return the old value
--
--     takeArray :: M (V.Vector Int)
--     takeArray = swapP #theArray (V.new 0)
swapP :: (MonadState s m) => MLensLike' (With a) m s a -> m a -> m a
swapP f k = updateP f (\a -> (, a) <$> k)

-- | Tries to swap the location with the update thunk
-- If the location exists, return the old value
-- If the location doesn't exist, return nothing
trySwapP :: (MonadState s m) => MLensLike' (Compose Maybe (With a)) m s a -> m a -> m (Maybe a)
trySwapP f k = tryUpdateP f (\a -> ((,a)) <$> k)


mkGetter :: Functor m => MGetter x m s t a b -> s -> (a -> m x) -> m x
mkGetter l s f = fmap getConst $ getCompose $ l (Compose . fmap Const . f) s

nonP :: (Functor f, Monad m) => m a -> MLensLike' f m (Maybe a) a
nonP m k Nothing = Just <$> Compose (getCompose . k =<< m)
nonP _ k (Just a) = Just <$> k a

nonSet :: (Functor f, Monad m) => a -> MLensLike' f m (Maybe a) a
nonSet a = nonP (pure a)

type MGetter r m s t a b = (a -> Compose m (Const r) b) -> s -> Compose m (Const r) t

-- Most general monadic lenses
type MLensLike' f m s a = MLensLike f m s s a a
type MLensLike f m s t a b =(a -> Compose m f b) -> s -> Compose m f t
-- type MLens m s a = forall f. Traversable f => (a -> Compose m f a) -> s -> Compose m f s

-- Mutating lenses don't return anything because they update in-place
type LValLens m s a = forall f. Distributes m f => (a -> Compose m f a) -> s -> Compose m f ()
type LValLensLike f m s a = (a -> Compose m f a) -> s -> Compose m f ()

-- Mutating traversals don't return anything because they update in-place
type LValTraversal m s a = forall f. (Monoid (f ()), Applicative f, Distributes m f) => (a -> Compose m f a) -> s -> Compose m f ()

fmap2 :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
fmap2 f = fmap (fmap f)

newtype MArr m f a b = MArr { unMArr :: Kleisli (Compose m f) a b }
deriving instance (Functor m, Functor f) => Functor (MArr m f a)
deriving instance (Applicative m, Applicative f) => Applicative (MArr m f a)
deriving instance (Alternative m, Alternative f) => Alternative (MArr m f a)
deriving instance (Distributes m f, Monad m, Monad f) => Monad (MArr m f a)
deriving instance (Monad (Compose m f)) => Profunctor (MArr m f)
deriving instance (Monad (Compose m f)) => Choice (MArr m f)
deriving instance (MonadFix (Compose m f)) => Costrong (MArr m f)
deriving instance (Monad (Compose m f)) => Strong (MArr m f)
deriving instance (Monad (Compose m f), Distributive (Compose m f)) => Closed (MArr m f)

 --
-- newtype IMArr i m f a b = IMArr { unMArr :: i -> a -> m (f b) }
--    deriving (Alternative, Applicative, Functor, Monad, MonadPlus, Choice, Closed, Costrong, Profunctor, Strong, Rewrapped, Wrapped) via Kleisli (Compose m f) a b
-- type MArrI i m f a b = Kleisli (Compose ((->) i) (Compose m f)) a b

type LValTraversalLike f m s a = (Applicative f, Distributes m f) => (a -> Compose m f a) -> s -> Compose m f ()

data With s a = With s a
  deriving (Functor, Traversable, Foldable)
instance Applicative m => Distributes m (With s)
instance Monoid s => Applicative (With s) where
  pure = With mempty
  With l f <*> With r a = With (l <> r) (f a)
