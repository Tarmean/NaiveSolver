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
import Data.Mutable.Internal.MutZoom (JoinZoom (joinZoom), BaseMonad)
import Data.Mutable.Distributive
import Data.Profunctor
import Control.Arrow (Kleisli)
import Data.Distributive
import Control.Monad.Identity (IdentityT(..))
import Control.Monad.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Primitive (PrimMonad (..))

mjoin :: (HasMonad m f, Functor m) => m (f (m a)) -> f a
mjoin = mapMR (mapML id)

flattenNested :: (Monoid a, HasMonad m f, Foldable t, Applicative f, Applicative m) => t (f (m a)) -> f (m a)
flattenNested = foldl1 (liftA2 $ liftA2 (<>))

mlens :: (JoinR m1 f, JoinL m2 f, Functor m1) => (s -> b -> m2 t) -> (s -> m1 a) -> (a -> f b) -> s -> f t
mlens setter getter f m = mapMR (mapML (setter m) . f) (getter m)

-- mtraverse :: (s -> (b -> f t) -> f t) -> s -> f t

-- mtraversal 

maffine :: forall m f s a. (HasMonad m f, Functor m, Applicative f) => (s -> a -> m ()) -> (s -> m (Maybe a)) -> (a -> f a) -> s -> f ()
maffine setter getter f m = mapMR (\case
     Just o -> mapML (setter m) (f o)
     Nothing -> pure ())
     (getter m)

-- | A 'mutable borrow'
-- Treat an in-place lens as a normal lens by returning the old location
-- mut (#counters .$ ixM 1) .= 4
mut :: (Functor f) => LValLensLike f s a -> MLensLike' f s a
mut l k s = s <$ l k s

instance (Monad m, Monad f, Distributes m f) => Monad (Compose m f) where
    (Compose m) >>= f = Compose $ fmap join $ join (fmap (traverseD (getCompose . f)) m)
instance (MonadIO m, Applicative f, Monad (Compose m f)) => MonadIO (Compose m f) where
    liftIO m = Compose $ pure <$> liftIO m

-- | Compose a getter with an in-place
-- 
(.$) :: ((t1 -> Const (Ap f1 a1) b1) -> t2 -> Const (Ap f2 a2) b2) -> (t3 -> t1 -> f1 a1) -> t3 -> t2 -> f2 a2
(.$) l r f s = getAp . getConst $ l (Const . Ap . (\x -> r f x)) s


(<.>$) :: ((b -> WithIndex ix1 (Const (Ap f r)) y) -> s -> Const (Ap f r) t) -> ((a -> WithIndex ix2 f x) -> b -> f r) -> (a -> WithIndex (ix1, ix2) f x) -> s -> f r
(<.>$) l r f s = getAp . getConst $ l inner s
  where inner x = usingIndex $ \ix1 -> Const $ Ap $ r (\a -> usingIndex $ \ix2 -> giveIndex (ix1, ix2) (f a)) x

(<.$) :: ((b -> WithIndex ix1 (Const (Ap f r)) y) -> s -> Const (Ap f r) t) -> ((a -> f x) -> b -> f r) -> (a -> WithIndex ix1 f x) -> s -> f r
(<.$) l r f s = getAp . getConst $ l inner s
  where inner x = usingIndex $ \ix1 -> Const $ Ap $ r (\a ->  giveIndex ix1 (f a)) x

(.>$) :: ((b -> (Const (Ap f r)) y) -> s -> Const (Ap f r) t) -> ((a -> WithIndex ix2 f x) -> b -> f r) -> (a -> WithIndex ix2 f x) -> s -> f r
(.>$) l r f s = getAp . getConst $ l inner s
  where inner x = Const $ Ap $ r (\a -> usingIndex $ \ix2 -> giveIndex ix2 (f a)) x

infixr 9 .$
infixr 9 <.>$
infixr 9 <.$

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

(&.) :: (HasZoom m n s t, JoinZoom (Zoomed n c)) => ((t -> Compose (BaseMonad (Zoomed n c)) (Zoomed n c) t) -> s -> Compose (BaseMonad (Zoomed n c)) (Zoomed n c) s) -> n c -> m c
(&.) l m = pzoom flattenLens m
  where flattenLens l' s = joinZoom $ getCompose $ l (Compose . pure . l') s 

pzoom :: HasZoom m n a b => LensLike' (Zoomed n x) a b -> n x -> m x
pzoom = zoom
type HasZoom m n a b = (Zoom n m b a, ZoomConstraints m n a b)
class (MonadState a m, MonadState b n) => ZoomConstraints m n a b | m -> a, m b -> n, n -> b, n a -> m where
instance (MonadState a m, MonadState b n, ZoomConstraints m n a b) => ZoomConstraints m n a b

class CovHack a b | a -> b, b -> a
instance CovHack a b => CovHack a b
-- | Mutate a place, possibly returning a new value
-- #fooArray %- \v ->
--     V.ensureCapacity (V.length v + 1) v
infix 4 &->
infix 4 &=
infix 4 &.
(&->) :: MonadState s m => MLensLike' (IdentityT m) s a -> (a -> m a) -> m ()
(&->) = mutateP
(&=) :: MonadState s m => MLensLike' (IdentityT m) s a -> a -> m ()
(&=) l x = mutateP l (\_ -> pure x)

usingIxP :: MonadState s m => MGetterIx ix x m s t a b -> (ix -> a -> m x) -> m x
usingIxP l inj = do
  s <- get 
  mkGetterIx l s inj
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
mutateP :: MonadState s m => MLensLike' (IdentityT m) s a -> (a -> m a) -> m ()
mutateP l f = do
  s <- get
  s' <- runIdentityT $ l (IdentityT . f) s
  put s'

mapP :: MonadState s m => MLensLike' (IdentityT m) s a -> (a -> a) -> m ()
mapP l f = mutateP l (pure . f)

-- | Mutate a place and also return a value
updateP :: (MonadState s m) => MLensLike' (Compose m (With x)) s a -> (a -> m (a, x)) -> m x
updateP f k = do
  s <- get
  With x s' <- getCompose $ f (Compose . fmap (uncurry $ flip With) . k) s
  put s'
  pure x
tryUpdateP :: (MonadState s m) => MLensLike' (Compose m (Compose Maybe (With x))) s a -> (a -> m (a, x)) -> m (Maybe x)
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
swapP :: (MonadState s m) => MLensLike' (Compose m (With a)) s a -> m a -> m a
swapP f k = updateP f (\a -> (, a) <$> k)

-- | Tries to swap the location with the update thunk
-- If the location exists, return the old value
-- If the location doesn't exist, return nothing
trySwapP :: (MonadState s m) => MLensLike' (Compose m (Compose Maybe (With a))) s a -> m a -> m (Maybe a)
trySwapP f k = tryUpdateP f (\a -> ((,a)) <$> k)


mkGetter :: Functor m => MGetter x m s t a b -> s -> (a -> m x) -> m x
mkGetter l s f = fmap getConst $ getCompose $ l (Compose . fmap Const . f) s

nonP :: (Functor f, Functor m, JoinR m f) => m a -> MLensLike' f (Maybe a) a
nonP m k Nothing = Just <$> joinR (k <$> m)
nonP _ k (Just a) = Just <$> k a

nonSet :: (Applicative m, Functor f, JoinR m f) => a -> MLensLike' f (Maybe a) a
nonSet a = nonP (pure a)

type MGetter r m s t a b = (a -> Compose m (Const r) b) -> s -> Compose m (Const r) t

-- Most general monadic lenses
type MLensLike' f s a = MLensLike f s s a a
type MLensLike f s t a b =(a ->f b) -> s -> f t
-- type MLens m s a = forall f. Traversable f => (a -> Compose m f a) -> s -> Compose m f s

-- Mutating lenses don't return anything because they update in-place
-- type LValLens m s a = forall f. (a -> Compose m f a) -> s -> Compose m f ()
type LValLensLike f s a = (a -> f a) -> s -> f ()


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

newtype WithIndex i m a = WithIndex { getWithIndex :: ReaderT i m a }
  deriving (Functor, Applicative, Monad, Alternative) via (ReaderT i m)
  deriving (MonadTrans) via (ReaderT i)
instance (PrimMonad m) => PrimMonad (WithIndex i m) where
    type (PrimState (WithIndex i m)) =  PrimState m
    primitive f = WithIndex $ primitive f
instance Monad m => JoinR m (WithIndex i m)
instance (Monad m) => JoinL m (WithIndex i m)

usingIndex ::  (i -> m a) -> WithIndex i m a
usingIndex f = WithIndex (ReaderT f)
giveIndex :: i -> WithIndex i m a -> m a
giveIndex i (WithIndex (ReaderT m)) = m i

type MGetterIx ix r m s t a b = (a -> WithIndex ix (Compose m (Const r)) b) -> s -> (Compose m (Const r)) t

forIxP :: Functor m => s -> MGetterIx ix x m s t a b -> (ix -> a -> m x) -> m x
forIxP s l f = mkGetterIx l s f

usingPIx :: MonadState s m => MGetterIx ix x m s t a b -> (ix -> a -> m x) -> m x
usingPIx l inj = do
  s <- get 
  mkGetterIx l s inj
mkGetterIx :: (Functor f1, Functor f2) => ((t1 -> WithIndex t2 (Compose f2 (Const a1)) a2) -> t3 -> Compose f1 (Const b1) b2) -> t3 -> (t2 -> t1 -> f2 a1) -> f1 b1
mkGetterIx l s inj = fmap getConst $ getCompose $ l (\a -> usingIndex $ \cix ->  Compose . fmap Const $ inj cix a) s

mkTransIx :: ((t1 -> WithIndex t2 m a) -> t3 -> t4) -> t3 -> (t2 -> t1 -> m a) -> t4
mkTransIx l s inj = l (\a -> usingIndex $ \cix ->  inj cix a) s

forP :: t1 -> (t2 -> t1 -> IdentityT f a) -> t2 -> f a
forP s l f = runIdentityT (l f s)

-- alterP :: Monad f => s -> ((a -> WriterT x f a) -> s -> WriterT x f ()) -> (a -> WriterT x f a) -> f x
-- alterP s l f = l f s
